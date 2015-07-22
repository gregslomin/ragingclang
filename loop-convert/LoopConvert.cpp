//------------------------------------------------------------------------------
// Tooling sample. Demonstrates:
//
// * How to write a simple source tool using libTooling.
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <sstream>
#include <string>
#include <fstream>
#include <utility>
#include <map>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;
static llvm::cl::OptionCategory ToolingSampleCategory("Tooling Sample");

map<string, int> locals;
map<string, int> globals;
map<string, int> statics;

map<const FunctionDecl*, int> localCounts;
static int globalInc = 0;
static int staticInc = 0;
static int localInc = 2;


// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.

uint32_t getSizeOfType(const Type* type);
uint64_t getSizeOfQualType(const QualType *type) {
    int mult = 1;
    if((*type)->isArrayType()) {
        const ArrayType *arr = (*type)->getAsArrayTypeUnsafe();
        if(isa<ConstantArrayType>(arr)) {
            const ConstantArrayType *cArrType = cast<const ConstantArrayType>(arr);
            mult = cArrType->getSize().getSExtValue();
        }
        
    }
    const Type *canonical = type->getCanonicalType().getTypePtr();
    if(canonical->getBaseElementTypeUnsafe()->isCharType() && mult >= 4) {
        return 1*mult + ((mult % 4 != 0) ? 1 : 0);
    }else if(canonical->isArrayType())
        return getSizeOfType(canonical->getArrayElementTypeNoTypeQual())*mult + (mult > 1 ? 4 :0);
    else
            return getSizeOfType(canonical)*mult + (mult > 1 ? 4 :0);
}


uint32_t getSizeOfCXXDecl(const CXXRecordDecl *classDecl, bool incVTableDef = false, bool incOwnVTable = false, const CXXRecordDecl *stopAt=NULL, bool *bFound = NULL) {
    incOwnVTable = true;
    if(classDecl == stopAt)
        return 0;
    
    uint64_t offset = 0;
    bool printedVTP = false;
    bool didAlloc = false;
    
    if(bFound == NULL) {
        didAlloc = true;
        bFound = new bool;
    }
    
    for(auto VBI : classDecl->bases()) {
        
        const CXXBaseSpecifier baseSpec = VBI;
        const CXXRecordDecl *baseDecl = baseSpec.getType()->getAsCXXRecordDecl();
        
        if(stopAt != NULL)
            if(baseDecl->getDeclName() == stopAt->getDeclName()) {
                *bFound = true;
                return offset;
            }
        
        
        offset += getSizeOfCXXDecl(baseDecl, incVTableDef, true, stopAt, bFound);
        if(*bFound)
            return offset;
        }
    
    
    printedVTP = false;
    if(incOwnVTable) {
        for(CXXMethodDecl *VFI : classDecl->methods()) {
            if(VFI->isVirtualAsWritten() && VFI->isFirstDecl()) {
                if(!printedVTP) {
                    offset+=4;
                    printedVTP = true;
                }
                if(incVTableDef)
                    offset+=4;
                else
                    break;
            }
        }
    }
    
    if(classDecl->isUnion()) {
        
        for(const FieldDecl *CS : classDecl->fields()) {
            if(CS->Decl::isFirstDecl() == false)
                continue;
            
            
            
            
            const  QualType type = CS->getType();
            int temp = getSizeOfQualType(&type);
            temp = max(temp, 4);
            
            if(temp > (int)offset)
                offset = temp;
            
        }
    } else {
    for(const FieldDecl *CS : classDecl->fields()) {
        if(CS->Decl::isFirstDecl() == false)
            continue;
        
        
        
        
        const  QualType type = CS->getType();
        int temp = getSizeOfQualType(&type);
        offset += max(temp, 4);
    }
    }
    
    return offset;
}
uint32_t getSizeOfVTable(const CXXRecordDecl *classDecl) {
    uint32_t size = 0;
    for(CXXMethodDecl *VFI : classDecl->methods()) {
        if(VFI->isVirtual()) {
            size++;
        }
    }
    return size;
}


uint32_t getNumVirtMethods(const CXXRecordDecl *classDecl) {
    int numVirt = 0;
    for(CXXMethodDecl *VFI : classDecl->methods())
        if(VFI->isVirtual())
            numVirt++;
    
    return numVirt;
}
uint32_t getSizeOfType(const Type* type) {
    
    if(type->isCharType()) {
        return 1;
} else if(isa<ConstantArrayType>(type)) {
    const ConstantArrayType *arrType = cast<const ConstantArrayType>(type);
    
        return getSizeOfType(type->getArrayElementTypeNoTypeQual())*(arrType->getSize()).getSExtValue();
    } else if(type->isRecordType() && type->getAsCXXRecordDecl()) {
        CXXRecordDecl *recordDecl = type->getAsCXXRecordDecl();
        return getSizeOfCXXDecl(recordDecl, true, false);
    }else if(type->isStructureType()) {
        const RecordType *record = type->getAsStructureType();
        
        if(RecordDecl *rd = record->getDecl()) {
            
            int size = 0;
            for(const auto *CS : rd->fields()) {
                const  QualType type = CS->getType();
                int temp = getSizeOfQualType(&type);

                size += max(temp, 4);
            }
            return size;
        }
        
    }else if(type->isIntegerType() || type->isBooleanType() || type->isCharType() || type->isFloatingType() || type->isPointerType()) {
        return 4;
    } else if(type->isVoidType()) {
        return 0;
    }else {
        return 0;
    }
    return 0;
}


uint32_t getSizeFromBytes(uint64_t bytes) {
    uint32_t size = (bytes/4) + ((bytes%4) ? 1 : 0);
    return size;
}

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
    MyASTVisitor(Rewriter &R, ASTContext *context, string filename) : TheRewriter(R), context(context), outfile(filename) {}
    
    //    bool VisitStmt(Stmt *s) {
    //        // Only care about compound statements.
    //
    //
    //        return true;
    //    }
    //
    
    
    bool handleParmVarDecl(ParmVarDecl *D) {
        if(isa<ParmVarDecl>(D)) {
            ParmVarDecl *decl = cast<ParmVarDecl>(D);
            if(isa<VarDecl>(decl)) {
                VarDecl *var = cast<VarDecl>(decl);
                
                auto size  = context->getTypeInfoDataSizeInChars(var->getType()).first.getQuantity();
                uint32_t oldLocalInc = localInc;
                locals.insert(make_pair(var->getName().str(), localInc));
                if(var->isCXXInstanceMember())
                    localInc += getSizeFromBytes(getSizeOfCXXDecl(var->getType()->getAsCXXRecordDecl(), true, false));
                else
                    localInc+=getSizeFromBytes(size);
                const Expr *initializer = var->getAnyInitializer();
                if(initializer) {
                    if(isa<CXXConstructExpr>(initializer)) {
                        
                        out << pFrame(oldLocalInc) << " //" << var->getNameAsString() << endl;
                        parseExpression(initializer);
                    } else {
                        parseExpression(initializer);
                        out << frameSet(oldLocalInc) << "  //" << var->getName().str() <<endl;
                    }
                }
            }
        }
        return true;
    }
    
    string frameSet(int index) {
        if((index & 0xFF) == index) {
            return "setFrame1 " + to_string(index);
        } else if((index & 0xFFFF) == index) {
            return "setFrame2 " + to_string(index);
        } else {
            assert(!"Frame Index out of range");
        }
    }
    
    string frameGet(int index) {
        if((index & 0xFF) == index) {
            return "GetFrame1 " + to_string(index);
        } else if((index & 0xFFFF) == index) {
            return "GetFrame2 " + to_string(index);
        } else {
            assert(!"Frame Index out of range");
        }
    }
    string dumpName(const NamedDecl *ND) {
        if(isa<CXXMethodDecl>(ND)) {
            const CXXMethodDecl *method = cast<const CXXMethodDecl>(ND);
            const CXXRecordDecl *record = method->getParent();
            return "@" + record->getNameAsString() + "::" + method->getNameAsString();
        }
        if (ND->getDeclName()) {
            
            return ND->getNameAsString();
        }
        return "";
    }
    
    string pFrame(const int index) {
        if((index & 0xFF) == index)
            return "pFrame1 " + to_string(index);
        else if((index&0xFFFF) == index)
            return "pFrame2 " + to_string(index);
        else
            return "Index too large";
        
    }
    
    void printDeclWithKey(string key, bool isAddr, bool isLtoRValue, int size = 1) {
        int index = -1;
        
        if(size > 1 && isLtoRValue) {
            out << "iPush " << size << "//size" << endl;
            isAddr = true;
        }
        
        
        if(locals.find(key) != locals.end()) {
            index = locals[key];
            if(isLtoRValue && !isAddr){
                out << frameGet(index) << " //" << key << endl;
            }
            else if(isAddr)
                out << pFrame(index) << " //&" << key << endl;
            else {
                out << frameSet(index) << " //" << key << endl;

            }
 

        }
        else if(globals.find(key) != globals.end()){
            index = globals[key];
            if(isLtoRValue && !isAddr)
                out << "GlobalGet3 ";
            else if(isAddr)
                out << "GlobalGetp ";
            else
                out << "GlobalSet3 ";
            out << index << "  //" << key << endl;
        } else if(statics.find(key) != statics.end()) {
            index = statics[key];
            if(isLtoRValue && !isAddr)
                out << "StaticGet2 ";
            else if(isAddr)
                out << "StaticGetP ";
            else
                out << "StaticSet2 ";
            out << index << "  //" << key << endl;
        }else {
            out << "DeclRefExpr not implemented" << endl;
        }
        
        if(size > 1 && isLtoRValue) {
            out << "ArrayToStack" << endl;
        }

    }
    
    bool parseStatement(Stmt *s, uint64_t breakLoc=-1, uint64_t continueLoc=-1) {
        if(isa<CompoundStmt>(s)) {
            CompoundStmt *cSt = cast<CompoundStmt>(s);
            //            cSt->dump();
            for (auto *CS : cSt->body()){
                if(isa<Stmt>(*CS))
                    parseStatement(cast<Stmt>(CS), breakLoc, continueLoc);
                else if(isa<Expr>(CS))
                    parseExpression(cast<const Expr>(CS));
            }
        } else if(isa<DeclStmt>(s)) {
            DeclStmt *decl = cast<DeclStmt>(s);
            handleDecl(decl);
        }else if (isa<IfStmt>(s)) {
            IfStmt *IfStatement = cast<IfStmt>(s);
            Expr *conditional = IfStatement->getCond();
            Stmt *Then = IfStatement->getThen();
            Stmt *Else = IfStatement->getElse();
            
            parseExpression(conditional, false, true);
            out << "JumpFalse @" << (Else ? Else->getLocStart().getRawEncoding() : s->getLocEnd().getRawEncoding()) << endl;
            
            parseStatement(Then, breakLoc, continueLoc);
            out << "Jump @" << s->getLocEnd().getRawEncoding() << endl;
            
            if(Else) {
                out << endl << ":"<< Else->getLocStart().getRawEncoding() <<endl;
                parseStatement(Else, breakLoc, continueLoc);
                s->getLocEnd().getRawEncoding();
            }
            out << endl << ":"<< s->getLocEnd().getRawEncoding() <<endl;
            
            
        } else if(isa<WhileStmt>(s)) {
            WhileStmt *whileStmt = cast<WhileStmt>(s);
            Expr *conditional = whileStmt->getCond();
            
            Stmt *body = whileStmt->getBody();
            
            out << endl << ":" << conditional->getLocStart().getRawEncoding() << endl;
            parseExpression(conditional, false, true);
            out << "JumpFalse @" << whileStmt->getLocEnd().getRawEncoding()  << endl;
            parseStatement(body, whileStmt->getLocEnd().getRawEncoding(), conditional->getLocStart().getRawEncoding());
            out << "Jump @" << conditional->getLocStart().getRawEncoding() << endl;
            out << endl << ":" << whileStmt->getLocEnd().getRawEncoding()  <<endl;
        }else if(isa<ForStmt>(s)) {
            ForStmt *forStmt = cast<ForStmt>(s);
            Stmt *decl = forStmt->getInit();
            Expr *conditional = forStmt->getCond();
            Expr *increment = forStmt->getInc();
            Stmt *body = forStmt->getBody();
            if(decl) {
                if(isa<DeclStmt>(decl)) {
                    handleDecl(cast<DeclStmt>(decl));
                }
            }
            
            if(conditional) {
            out << endl << ":"<<conditional->getLocStart().getRawEncoding() << endl;

                parseExpression(conditional);
                if(increment)
                    out << "JumpFalse @" << increment->getLocEnd().getRawEncoding()  << endl;
                else
                    out << "JumpFalse @" << body->getLocEnd().getRawEncoding()  << endl;
            }

            parseStatement(body, forStmt->getLocEnd().getRawEncoding(), (conditional ? conditional->getLocStart().getRawEncoding() : body->getLocStart().getRawEncoding()));
            if(increment)
                parseExpression(increment);
            if(conditional)
                out << "Jump @" << conditional->getLocStart().getRawEncoding() << endl;
            else
                out << "Jump @" << body->getLocStart().getRawEncoding() << endl;
            if(increment)
                out << endl << ":"<< increment->getLocEnd().getRawEncoding() <<endl;
            else
                out << endl << ":"<< body->getLocEnd().getRawEncoding() <<endl;
            
        } else if(isa<UnaryOperator>(s)) {
            parseExpression(cast<const Expr>(s));
        } else if(isa<DoStmt>(s)) {
           DoStmt *doStmt = cast<DoStmt>(s);
           Expr *conditional = doStmt->getCond();
            
            Stmt *body = doStmt->getBody();
            

             out << endl << ":" << body->getLocStart().getRawEncoding()  <<endl;

            parseStatement(body, conditional->getLocEnd().getRawEncoding(), body->getLocStart().getRawEncoding());
            
           
            
            
            out << endl << ":" << conditional->getLocStart().getRawEncoding() << "" <<endl;
            parseExpression(conditional);
            out << "not //Invert Result" << endl;
            out << "JumpFalse @" << body->getLocStart().getRawEncoding() <<endl;
            out << endl << ":" << conditional->getLocEnd().getRawEncoding() << "" <<endl;
            
        }else if(isa<ReturnStmt>(s)) {
            const ReturnStmt *ret = cast<const ReturnStmt>(s);
            const Expr* retVal = ret->getRetValue();
            if(retVal)
                parseExpression(retVal, false, true);
            int size = 0;
            if(ret->getRetValue()){
            QualType type = ret->getRetValue()->getType();
            size = context->getTypeInfoDataSizeInChars(type).first.getQuantity();
            }
            
            int paramSize = 0;
            for(int i=0; i<currFunction->getNumParams(); i++) {
                paramSize += getSizeFromBytes(getSizeOfType(currFunction->getParamDecl(i)->getType().getTypePtr()));
            }
            out << "Return " << paramSize + (isa<CXXMethodDecl>(currFunction) ? 1 : 0) << " " << getSizeFromBytes(size) << endl;
        } else if(isa<Expr>(s)) {
            parseExpression(cast<const Expr>(s));
        } else if(isa<BreakStmt>(s)) {
            out << "Jump @" << breakLoc << endl;
        }else if(isa<NullStmt>(s)) {
           // out << "nop " << breakLoc << endl;
        } else if(isa<ContinueStmt>(s)) {
            out << "Jump @" << continueLoc << endl;
        } else if(isa<DefaultStmt>(s)) {
//            DefaultStmt *stmt = cast<DefaultStmt>(s);
//            parseStatement(stmt->getSubStmt(), breakLoc);
        }else if(isa<CaseStmt>(s)) {
            CaseStmt *caseS = cast<CaseStmt>(s);

                Expr *LHS = caseS->getLHS();
            if(isa<CastExpr>(LHS)) {
                LHS = cast<CastExpr>(LHS)->getSubExpr();
            }
                if(isa<IntegerLiteral>(LHS)) {
                    IntegerLiteral *literal = cast<IntegerLiteral>(LHS);
                    out << "case @" << literal->getValue().getSExtValue() << endl;

                   // caseS->dump()
                } else if(isa<FloatingLiteral>(LHS)) {
                    FloatingLiteral *literal = cast<FloatingLiteral>(LHS);
                    out << "case @" << literal->getValue().convertToFloat() << endl;
                }
            
            if(caseS->getRHS())
                parseExpression(caseS->getRHS());
            
            if(caseS->getSubStmt())
                parseStatement(caseS->getSubStmt(), breakLoc);

        
            
        }else if(isa<SwitchStmt>(s)) {
            SwitchStmt *switchStmt = cast<SwitchStmt>(s);
            
            out << "//Switch Conditional" << endl;
            parseExpression(switchStmt->getCond());
            
            
            out << "SwitchStart" << endl;
            SwitchCase *switchCase = switchStmt->getSwitchCaseList();
            

            
            while(switchCase != NULL) {
                if(isa<DefaultStmt>(switchCase)) {
                    DefaultStmt *stmt = cast<DefaultStmt>(switchCase);
                    parseStatement(stmt->getSubStmt(), breakLoc);
                    out << "Jump @" << switchStmt->getLocEnd().getRawEncoding() << endl;
                    break;
                }
                switchCase = switchCase->getNextSwitchCase();
            }
            parseStatement(switchStmt->getBody(), switchStmt->getLocEnd().getRawEncoding());
            out << "SwitchEnd" << endl << endl;
            out << ":" << switchStmt->getLocEnd().getRawEncoding() << endl;
        }else {
            out << "Unhandled Stmt" << endl;
        }
        return true;
    }
    
    bool handleDecl(DeclStmt* decl) {
        for (DeclStmt::decl_iterator I = decl->decl_begin(), E = decl->decl_end(); I != E; ++I) {
            if(isa<VarDecl>(*I)) {
                VarDecl *var = cast<VarDecl>(*I);
                
                auto size  = context->getTypeInfoDataSizeInChars(var->getType()).first.getQuantity();
                uint32_t oldLocalInc = localInc;
                locals.insert(make_pair(var->getName().str(), localInc));
                
                const ArrayType *arr = NULL;
                if((arr=var->getType()->getAsArrayTypeUnsafe()) && arr->getArrayElementTypeNoTypeQual()->getAsCXXRecordDecl()) {
                    if(isa<ConstantArrayType>(arr)) {
                        const ConstantArrayType *cArrType = cast<const ConstantArrayType>(arr);
                        size = getSizeOfCXXDecl(arr->getArrayElementTypeNoTypeQual()->getAsCXXRecordDecl(), true, false ) * cArrType->getSize().getSExtValue();
                        localInc += getSizeFromBytes(size);
                    } else {
                        out << "Unsupported decl" << endl;
                    }

                }else if(var->getType()->getAsCXXRecordDecl()) {
                    size = getSizeOfCXXDecl(var->getType()->getAsCXXRecordDecl(), true, false );
                    localInc += getSizeFromBytes(size);
                }
                else
                    localInc+=getSizeFromBytes(size);
                
                const Expr *initializer = var->getAnyInitializer();
                if(initializer) {
                    if(isa<CXXConstructExpr>(initializer)) {
                        if(isa<ConstantArrayType>(var->getType())) {
                            const ConstantArrayType *arr = cast<ConstantArrayType>(var->getType());
                            static int vTableInitInc = 0;

                            out << "iPush 0" << endl;
                            out << ":vTableConditional_" << vTableInitInc << endl;
                            //for(int i=0; i<arr->getSize().getSExtValue(); i++) {
                                out << "dup //index" << endl;
                                out << "iPush " << arr->getSize().getZExtValue() << endl;
                                out << "icmplt" << endl;
                                out << "JumpFalse @vTableEnd_" << vTableInitInc << endl;
                                
                                out << "dup #index" << endl;
                                out << pFrame(oldLocalInc) << " //" << var->getNameAsString() << endl;
                                out << "ArrayGetP " << getSizeFromBytes(getSizeOfCXXDecl(arr->getArrayElementTypeNoTypeQual()->getAsCXXRecordDecl(), true, true)) << "//index Array" << endl;
                                parseExpression(initializer, true, false, true, var);
                                out << "iPush 1" << endl;
                                out << "addi" << endl;
                                out << "Jump @vTableConditional_" << vTableInitInc << endl;
                                out << ":vTableEnd_" << vTableInitInc << endl << endl;
                            //}
                            vTableInitInc++;
                            return true;
                        }
                        out << pFrame(oldLocalInc) << " //" << var->getNameAsString() << endl;
                        parseExpression(initializer, true, false, true, var);
                        return true;
                    }

                    parseExpression(initializer, false, true);
                    if(size > 4) {
                        out << "iPush " << size/4 << " //Type Size" << endl;
                        out << pFrame(oldLocalInc) << " //&" << var->getNameAsString() << endl;
                        out << "ArrayFromStack " << endl;
                    } else {
                        out << frameSet(oldLocalInc) << "  //" << var->getName().str() << endl;
                    }
                }
            }
        }
        return true;
    }
    
    
    bool checkIntrinsic(const CallExpr *call) {
        string funcName = parseCast(cast<const CastExpr>(call->getCallee()));
        const Expr * const*argArray = call->getArgs();
        if(funcName == "@__strcpy") {
            parseExpression(argArray[1]);
            parseExpression(argArray[0]);

            
            out << "scpy ";
            
            if(isa<IntegerLiteral>(argArray[2])) {
                const IntegerLiteral *literal = cast<const IntegerLiteral>(argArray[2]);
                out << literal->getValue().getSExtValue() << endl;
            } else if(isa<CastExpr>(argArray[2])) {
                out << parseCast(cast<const CastExpr>(argArray[2])) << endl;
            }
            return true;
        }
        return false;
    }

    
    string parseCast(const CastExpr *castExpr) {
        switch(castExpr->getCastKind()) {
            case clang::CK_LValueToRValue:
                break;
            case clang::CK_IntegralCast:
            {
                const Expr *e = castExpr->getSubExpr();
                if(isa<IntegerLiteral>(e)) {
                    const IntegerLiteral *literal = cast<const IntegerLiteral>(e);
                    return to_string(literal->getValue().getSExtValue());
                } else if(isa<FloatingLiteral>(e)) {
                    const FloatingLiteral *literal = cast<const FloatingLiteral>(e);
                    if(&literal->getValue().getSemantics() == &llvm::APFloat::IEEEsingle)
                        return to_string(literal->getValue().convertToFloat());
                    else
                        return to_string(literal->getValue().convertToDouble());
                } else {
                    out << "unhandled cast" << endl;
                }
            }
            case clang::CK_FunctionToPointerDecay:
            {
                if(isa<DeclRefExpr>(castExpr->getSubExpr())) {
                    const DeclRefExpr *declRef = cast<const DeclRefExpr>(castExpr->getSubExpr());
                    if(isa<FunctionDecl>(declRef->getDecl())) {
                       const FunctionDecl *decl = cast<const FunctionDecl>(declRef->getDecl());
                        return getNameForFunc(decl);
                    } else {
                        out << "Unimplemented cast" << endl;
                    }

                } else {
                    out << "Unimplemented cast" << endl;
                }
            }
                break;
            default:
                out << "unimplemented cast" << endl;
        }
        return "";
    }
    
    string getNameForFunc(const FunctionDecl *decl) {
        if(isa<CXXMethodDecl>(decl)) {
            const CXXMethodDecl *methodDecl = cast<const CXXMethodDecl>(decl);
            const CXXRecordDecl *record = methodDecl->getParent();
            return "@" + record->getNameAsString() + "::" + methodDecl->getNameAsString();
        } else {
            return "@"+decl->getNameAsString();
        }
    }
    
    
    const DeclRefExpr *getDeclRefExpr(const Expr *e) {
        if(isa<DeclRefExpr>(e)) {
            return cast<const DeclRefExpr>(e);
        } else {
            for(auto *CS : e->clang::Stmt::children()) {
                if(isa<Expr>(CS)) {
                    return getDeclRefExpr(cast<const Expr>(CS));
                }
            }
        }
        return NULL;
    }
    
    
    int parseExpression(const Expr *e, bool isAddr = false, bool isLtoRValue = false, bool printVTable = true, const NamedDecl *lastDecl=NULL) {
        if(isa<IntegerLiteral>(e)) {
            const IntegerLiteral *literal = cast<const IntegerLiteral>(e);
            out << iPush(literal->getValue().getSExtValue()) << endl;
        } else if(isa<FloatingLiteral>(e)) {
            const FloatingLiteral *literal = cast<const FloatingLiteral>(e);
            if(&literal->getValue().getSemantics() == &llvm::APFloat::IEEEsingle)
                out << "fPush " << (double)literal->getValue().convertToFloat() << endl;
            else
                out << "fPush " << literal->getValue().convertToDouble() << endl;
        } else if(isa<CompoundLiteralExpr>(e)) {
            const CompoundLiteralExpr *cLit = cast<const CompoundLiteralExpr>(e);
            if(isa<InitListExpr>(cLit->getInitializer())) {
                const InitListExpr *init = cast<const InitListExpr>(cLit->getInitializer());
                for(unsigned int i=0; i<init->getNumInits(); i++) {
                    parseExpression(init->getInit(i));
                }
               // if(!printVTable)
               //     out << "iPush " << init->getNumInits() << " // numInitializers" << endl;
            } else {
                parseExpression(cLit->getInitializer());
//                out << "Unimplemented CompoundLiteralExpr" << endl;
            }
        }else if(isa<StringLiteral>(e)) {
            const StringLiteral *literal = cast<const StringLiteral>(e);
            if(literal->getString().str().length() > 0)
                out << "PushString \"" << literal->getString().str() << "\"" << endl;
            else
                out << "PushString \"\"" << endl;
        }else if(isa<CallExpr>(e)) {
            const CallExpr *call = cast<const CallExpr>(e);
                                if(checkIntrinsic(call))
                                    return 1;
            const Expr * const*argArray = call->getArgs();
            for(int i=0; i<call->getNumArgs(); i++) {
                parseExpression(argArray[i], false, true);
            }

            if(isa<CastExpr>(call->getCallee()))
                if(call->getDirectCallee()->isDefined())
                    out << "Call " << parseCast(cast<const CastExpr>(call->getCallee())) << " //NumArgs: " << call->getNumArgs() << " " << endl;
                else {

                    const QualType type = call->getDirectCallee()->getReturnType();
                    out << "CallNative " << parseCast(cast<const CastExpr>(call->getCallee())) << " " << call->getNumArgs() << " " << getSizeFromBytes(getSizeOfQualType(&type)) << endl;

//                    }
                }
            else if(isa<MemberExpr>(call->getCallee())) {
                const MemberExpr *expr = cast<const MemberExpr>(call->getCallee());
                if(isa<CXXMethodDecl>(expr->getMemberDecl())) {
                    const CXXMethodDecl *method = cast<const CXXMethodDecl>(expr->getMemberDecl());
                    if(method->isVirtualAsWritten()) {
                        const CXXRecordDecl *classDecl = method->getParent();


                        int offset = 0;
                        printVirtualCall(classDecl, method, expr->getBase());
                    } else {

                        parseExpression(expr->getBase(), true);
                        out << "call " << getNameForFunc(method) << " //NumArgs: " << call->getNumArgs()+1 << " " << endl;
                    }
                }else {
                    out << "Unhandled Call Member Expression" << endl;
                }
            }
            else
                out << "Unimplemented call" << endl;
            
            
            if(call->getType()->isVoidType() == false) {
                if(!isLtoRValue) {
                    out << "pop //Function Result unused" << endl;
                call->dump();
                }
            }
            
        }else if(isa<CastExpr>(e)) {
            const CastExpr *icast = cast<const CastExpr>(e);
            switch(icast->getCastKind()){
                case clang::CK_IntegralToFloating:
                {
                    if(isa<IntegerLiteral>(icast->getSubExpr())) {
                        const IntegerLiteral *literal = cast<const IntegerLiteral>(icast->getSubExpr());
                        out << "fPush " << literal->getValue().getSExtValue() << ".0" << endl;
                        return true;
                    } else {
                        parseExpression(icast->getSubExpr(), false, true);
                        out << "itof" <<endl;
                        return true;
                    }
                }
                case clang::CK_FloatingCast:
                case clang::CK_IntegralCast:
                    parseExpression(icast->getSubExpr(), isAddr, isLtoRValue);
                    break;
                case clang::CK_ArrayToPointerDecay:
                    parseExpression(icast->getSubExpr(), true, false);
                    break;
                case clang::CK_LValueToRValue:
                {
                    parseExpression(icast->getSubExpr(), isAddr, true, printVTable);
                   //const Expr *subE = icast->getSubExpr();

                    //handleRValueDeclRef(subE);
                    break;
                }
                case clang::CK_UncheckedDerivedToBase:
                {
                    if(isa<DeclRefExpr>(icast->getSubExpr())) {
                        const DeclRefExpr *declRef = cast<const DeclRefExpr>(icast->getSubExpr());
                        CXXRecordDecl *base = declRef->getType()->getAsCXXRecordDecl();
                        int offset = getSizeOfCXXDecl(base, false, false, icast->getType()->getAsCXXRecordDecl());
                        if(offset != 0) {
                        out << endl  << iPush(offset/4) << " //Base+" << offset << endl;
                        parseExpression(declRef, true);
                        out << "ArrayGetP 1  " << " //Cast : " << base->getDeclName().getAsString() << " to " << icast->getType()->getAsCXXRecordDecl()->getDeclName().getAsString() << endl;
                        } else {
                            parseExpression(icast->getSubExpr());
                        }
                    }
                    else if(isa<CXXThisExpr>(icast->getSubExpr())){
                        const CXXThisExpr *expr = cast<const CXXThisExpr>(icast->getSubExpr());
                        const PointerType *pointer = cast<const PointerType>(expr->getType());
                        const PointerType *castPointer = cast<const PointerType>(icast->getType());
                        
                        CXXRecordDecl *base = pointer->getPointeeType()->getAsCXXRecordDecl();
                        int offset = getSizeOfCXXDecl(base, false, false, castPointer->getPointeeCXXRecordDecl());
                        if(offset != 0) {
                        out << endl << iPush( offset/4) << " //Base+" << offset << endl;
                        parseExpression(expr, true);
                            if(icast->getType()->getAsCXXRecordDecl())
                            out << "ArrayGetP 1  " << " //Cast : " << base->getDeclName().getAsString() << " to " << icast->getType()->getAsCXXRecordDecl()->getDeclName().getAsString() << endl;
                            else
                                    out << "ArrayGetP 1  " << " //Cast : " << base->getDeclName().getAsString() << " to " << icast->getType()->getPointeeCXXRecordDecl()->getDeclName().getAsString() << endl;
                        } else {
                                parseExpression(icast->getSubExpr());
                        }
                    } else {
                        out << "unsupported cast" << endl;
                    }
                        
                    
                    break;
                    
                }
                case clang::CK_DerivedToBase:
                {
                    parseExpression(icast->getSubExpr());
                    break;
                }
                case clang::CK_PointerToIntegral:
                {
                    
                    parseExpression(icast->getSubExpr());
                    break;
                }
                case clang::CK_FloatingToIntegral:
                {
                    
                    parseExpression(icast->getSubExpr());
                    out << "CallNative @FLOOR 1 0" << endl;
                    break;
                }
                case clang::CK_NoOp:
                {
                    parseExpression(icast->getSubExpr());
                    break;
                }
                case clang::CK_BitCast:
                {
                    parseExpression(icast->getSubExpr());
                    break;
                }
                default:
                    out << "Unhandled cast" << endl;
                    
            }
        }else if(isa<DeclRefExpr>(e)) {
            const DeclRefExpr *declref = cast<const DeclRefExpr>(e);
            
            if(isa<EnumConstantDecl>(declref->getDecl())) {
                const EnumConstantDecl *enumDecl = cast<const EnumConstantDecl>(declref->getDecl());
                int val = enumDecl->getInitVal().getSExtValue();
                out << iPush(val) << endl;
                return 1;
            }
            
            string key = declref->getNameInfo().getAsString();
            printDeclWithKey(key, isAddr, isLtoRValue, getSizeFromBytes(getSizeOfType(declref->getType().getTypePtr())));
            
            return true;
        }else if(isa<ArraySubscriptExpr>(e)) {
            return parseArraySubscriptExpr(e, isAddr, isLtoRValue);
        }else if(isa<ParenExpr>(e)) {
            const ParenExpr *parenExpr = cast<const ParenExpr>(e);
            parseExpression(parenExpr->getSubExpr(), isAddr, isLtoRValue);
        }else if(isa<UnaryOperator>(e)) {
            const UnaryOperator *op = cast<const UnaryOperator>(e);
            
            Expr *subE = op->getSubExpr();
            if(op->getOpcode() == UO_Minus) {
                if(isa<IntegerLiteral>(subE)) {
                    const IntegerLiteral *literal = cast<const IntegerLiteral>(subE);
                    out << iPush(-(literal->getValue().getSExtValue())) << endl;
                }else if(isa<FloatingLiteral>(subE)) {
                    const FloatingLiteral *literal = cast<const FloatingLiteral>(subE);
                    
                    out << "fPush ";
                    if(&literal->getValue().getSemantics() == &llvm::APFloat::IEEEsingle)
                        out << to_string(-1.0f*literal->getValue().convertToFloat());
                    else
                        out << to_string(-1.0*literal->getValue().convertToDouble());
                    out << endl;
                   // out << "fPush " << (double)-(literal->getValue().convertToDouble()) << endl;
                }
                return false;
            } else if(op->getOpcode() == UO_LNot) {
                if(isa<IntegerLiteral>(subE)) {
                    const IntegerLiteral *literal = cast<const IntegerLiteral>(subE);
                    out << iPush(-(literal->getValue().getSExtValue())) << endl;
                    
                }else if(isa<FloatingLiteral>(subE)) {
                    const FloatingLiteral *literal = cast<const FloatingLiteral>(subE);
                    out << "fPush " << (double)-(literal->getValue().convertToDouble()) << endl;
                    
                } else if(isa<Expr>(subE)) {
                    parseExpression(subE, isAddr, isLtoRValue);
                    
                } else {
                    out << "unimplmented UO_Not" << endl;
                }
                out << "not" << endl;
                return true;
                
            } else if(op->getOpcode() == UO_AddrOf) {
                if(isa<ArraySubscriptExpr>(subE)) {
                    parseArraySubscriptExpr(subE, true);
                } else if(isa<DeclRefExpr>(subE)){
                    parseExpression(subE, true, false);
                } else {
                    parseExpression(subE, true, false);
                }
                return  true;
                
            } else if(op->getOpcode() == UO_Deref) {
                if(isa<ArraySubscriptExpr>(subE)) {
                    parseArraySubscriptExpr(subE, false);
                } else if(isa<DeclRefExpr>(subE)){
                    parseExpression(subE, false, false);
                } else {
                    parseExpression(subE, false, false);
                }
                if(isLtoRValue)
                    out << "pGet" << endl;
                else
                    out << "pSet" << endl;
                return true;
            }
            
 
            

            if(op->isPrefix()) {
                
                if(op->isIncrementOp()) {
                    parseExpression(subE, false, true);
                    out << "iPush 1" << endl;
                    out << "addi" << endl;
                    if(isLtoRValue)
                    out << "dup" << endl;
                    parseExpression(subE);
                                        return 1;
                } else if(op->isDecrementOp()) {
                    parseExpression(subE, false, true);
                    out << "iPush 1" << endl;
                    out << "subi" << endl;
                    if(isLtoRValue)
                    out << "dup" << endl;
                   parseExpression(subE);
                                       return 1;
                }
            } else if(op->isPostfix()) {
                if(op->isIncrementOp()) {
                    parseExpression(subE, false, true);
                    if(isLtoRValue)
                    out << "dup" << endl;
                    out << "iPush 1" << endl;
                    out << "addi" << endl;
                    parseExpression(subE, false, false);
                    return 1;
                } else if(op->isDecrementOp()) {
                    parseExpression(subE, false, true);

                    out << "iPush 1" << endl;
                    if(isLtoRValue)
                    out << "dup" << endl;
                    out << "subi" << endl;
                    parseExpression(subE, false, false);
                                        return 1;
                }
            }
        } else if(isa<CXXThisExpr>(e)) {
            out << "GetFrame1 0 //\"this\"" << endl;
        }else if(isa<CXXConstructExpr>(e)) {
            const CXXConstructExpr *expr = cast<const CXXConstructExpr>(e);
            if(printVTable) {


//                out << "\n//VTableInit " << endl;
                //out << "call "
                if(expr->getType()->isArrayType()){
                    out << "dup" << endl;
                    out << "call @" << expr->getType()->getAsArrayTypeUnsafe()->getArrayElementTypeNoTypeQual()->getAsCXXRecordDecl()->getNameAsString() << "::VTableInit" << endl;//printVTableInit(expr->getType()->getAsArrayTypeUnsafe()->getArrayElementTypeNoTypeQual()->getAsCXXRecordDecl(), lastDecl);
                } else {
                     out << "dup" << endl;
                
                    out << "call " << expr->getBestDynamicClassType()->getNameAsString() << "::VTableInit" <<endl;//printVTableInit(expr->getBestDynamicClassType(), lastDecl);
                }
              //  out << " //End_VtableInit\n" << endl;
            }
            if(expr->getConstructor()->hasBody())
                out << "call " << getNameForFunc(expr->getConstructor()) << " // ctor" << endl;
            
        }else if(isa<BinaryOperator>(e)) {
            const BinaryOperator *bOp = cast<const BinaryOperator>(e);
            
            if(bOp->getOpcode() == BO_Assign) {

                parseExpression(bOp->getRHS(), isAddr, true, false);
                if(bOp->getRHS()->getType()->isStructureOrClassType()) {
                    int size = getSizeFromBytes(getSizeOfType(bOp->getRHS()->getType().getTypePtr()));
                    out << "iPush " << size << " //size " << endl;
                    parseExpression(bOp->getLHS(), true);
                    
                    out << "ArrayFromStack" << endl;
                } else {
                    parseExpression(bOp->getLHS());
                }
                
                return true;
            }

            switch(bOp->getOpcode()) {
                case BO_SubAssign:
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS());
                    if(bOp->getLHS()->getType()->isFloatingType())
                        out << "f";
                    else
                        out << "i";
                    out << "sub" << endl;
                    parseExpression(bOp->getLHS(), false, false);
                    break;
                case BO_AddAssign:
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS());
                    if(bOp->getLHS()->getType()->isFloatingType())
                        out << "f";
                    else
                        out << "i";
                    out << "add" << endl;
                    parseExpression(bOp->getLHS(), false, false);
                    break;
                case BO_DivAssign:
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS());
                    if(bOp->getLHS()->getType()->isFloatingType())
                        out << "f";
                    else
                        out << "i";
                    out << "div" << endl;
                    parseExpression(bOp->getLHS(), false, false);
                    break;
                case BO_MulAssign:
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS());
                    if(bOp->getLHS()->getType()->isFloatingType())
                        out << "f";
                    else
                        out << "i";
                    out << "mul" << endl;
                    parseExpression(bOp->getLHS(), false, false);
                    break;
                case BO_OrAssign:
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS());
                    out << "or" << endl;
                    parseExpression(bOp->getLHS(), false, false);
                    break;
                default:
                {
                    parseExpression(bOp->getLHS(), false, true);
                    parseExpression(bOp->getRHS(), false, true);
                    
                    
                    if(bOp->getLHS()->getType()->isFloatingType()) {
                        switch(bOp->getOpcode()) {
                            case BO_EQ:
                                out << "fcmpeq" << endl;
                                break;
                            case BO_Mul:
                                out << "fmul" << endl;
                                break;
                            case BO_Div:
                                out << "fdiv" << endl;
                                break;
                            case BO_Rem:
                                out << "fmod" << endl;
                                break;
                            case BO_Sub:
                                out << "fsub" << endl;
                                break;
                            case BO_LT:
                                out << "fcmplt" << endl;
                                break;
                            case BO_GT:
                                out << "fcmpgt" << endl;
                                break;
                            case BO_GE:
                                out << "fcmpge" << endl;
                                break;
                            case BO_LE:
                                out << "fcmple" << endl;
                                break;
                            case BO_NE:
                                out << "fcmpne" << endl;
                                break;
                            case BO_LAnd:
                            case BO_And:
                                out << "iand" << endl;
                                break;
                            case BO_Xor:
                                out << "ixor" << endl;
                                break;
                            case BO_Add:
                                out << "fadd" << endl;
                                break;
                            case BO_LOr:
                            case BO_Or:
                                out << "or " << endl;
                                break;
                                
                            default:
                                out << "unimplemented2 " << bOp->getOpcode() << endl;
                        }

                    } else {
                    switch(bOp->getOpcode()) {
                        case BO_EQ:
                            out << "icmpeq" << endl;
                            break;
                        case BO_Mul:
                            out << "imul" << endl;
                            break;
                        case BO_Div:
                            out << "idiv" << endl;
                            break;
                        case BO_Rem:
                            out << "imod" << endl;
                            break;
                        case BO_Sub:
                            out << "isub" << endl;
                            break;
                        case BO_LT:
                            out << "icmplt" << endl;
                            break;
                        case BO_GT:
                            out << "icmpgt" << endl;
                            break;
                        case BO_GE:
                            out << "icmpge" << endl;
                            break;
                        case BO_LE:
                            out << "icmple" << endl;
                            break;
                        case BO_NE:
                            out << "icmpne" << endl;
                            break;
                        case BO_LAnd:
                        case BO_And:
                            out << "iand" << endl;
                            break;
                        case BO_Xor:
                            out << "ixor" << endl;
                            break;
                        case BO_Add:
                            out << "iadd" << endl;
                            break;
                        case BO_LOr:
                        case BO_Or:
                            out << "or " << endl;
                            break;
                            
                        default:
                            out << "unimplemented2 " << bOp->getOpcode() << endl;
                    }
                    }

                }
            }
                   } else if(isa<MemberExpr>(e)) {
            const MemberExpr *E = cast<const MemberExpr>(e);
            Expr *BaseExpr = E->getBase();

            
               if (E->isArrow()) {
                   parseExpression(BaseExpr, false);
                   
               } else
                   parseExpression(BaseExpr, true);
           
           
               

                int offset = 0;
                                   NamedDecl *ND = E->getMemberDecl();
                       

                                                  const CXXRecordDecl *classDecl = NULL;
                       if(isa<PointerType>(BaseExpr->getType().getTypePtr())) {
                           const PointerType *pointer = cast<const PointerType>(BaseExpr->getType().getTypePtr());
                           classDecl = pointer->getPointeeType()->getAsCXXRecordDecl();
                       }
                       if(classDecl){ //BaseExpr->getType()->getAsCXXRecordDecl() != NULL || isa<CXXThisExpr>(BaseExpr)) {

                           
//                           if(isa<CXXThisExpr>(BaseExpr)) {
//                               CXXThisExpr *thisExpr = cast<CXXThisExpr>(BaseExpr);
//                               classDecl = thisExpr->getBestDynamicClassType();
//                           }else {
//                               
//                           //classDecl = BaseExpr->getType()->getAsCXXRecordDecl();
//                             
//                           }
                             offset = getCXXOffsetOfNamedDecl(classDecl, ND);
                       } else {
                           
                           
                           if (auto *Field = dyn_cast<FieldDecl>(ND)) {
                               const RecordDecl *record = Field->getParent();
                               if(record->isUnion())
                                   offset = 0;
                               else {
                                   for(const auto *CS : record->fields()) {
                                       if(CS == Field)
                                           break;
                                       
                                       const  QualType type = CS->getType();
                                       int temp = getSizeOfQualType(&type);
                                       offset += max(temp, 4);
                                   }
                               }
                               
                               
                           }
                       }
                       

                

                       int size = getSizeFromBytes(offset);
                if(isLtoRValue)
                    out << "GetImm";
                else if(isAddr) {
                    out << "GetImmp "<< size <<  " // ." << ND->getName().str() << endl;;
                    return 1;
                }else
                    out << "SetImm";
                       
                       if((size & 0xFF) == size)
                           out << "1" ;
                       else if((size & 0xFFFF) == size)
                           out << "2" ;
                       else
                           out << "3" ;
                out << " " << size <<  " // ." << ND->getName().str() << endl;
                return 1;


            
           // out << "Unhandled member declaration" << endl;
//            
//            if (auto *VD = dyn_cast<VarDecl>(ND))
//                return EmitGlobalVarDeclLValue(*this, E, VD);
//            
//            if (const auto *FD = dyn_cast<FunctionDecl>(ND))
//                return EmitFunctionDeclLValue(*this, E, FD);
//            
//            llvm_unreachable("Unhandled member declaration!");
        }else {
            out << "unimplemented3 " << endl;
            
        }
        return -1;
    }
    
    uint32_t getCXXOffsetOfNamedDecl(const CXXRecordDecl *classDecl, const NamedDecl *ND, const CXXRecordDecl *prevDecl = NULL) {
        bool found = false;
        bool foundVirt = false;
        int offset = 0;
        
        for(auto VBI : classDecl->bases()) {
            
            const CXXBaseSpecifier baseSpec = VBI;
            const CXXRecordDecl *baseDecl = baseSpec.getType()->getAsCXXRecordDecl();
            

            offset += getCXXOffsetOfNamedDecl(baseDecl, ND, classDecl);
//            for(CXXMethodDecl *VFI : baseDecl->methods()) {
//                if(VFI->isVirtual()) {
//                    offset+=4;
//                    break;
//                }
//            }
//            for(const FieldDecl *CS : baseDecl->fields()) {
//                
//                if(CS->Decl::isFirstDecl() == false)
//                    continue;
//                if(CS == ND) {
//                    found = true;
//                }
//                
//                const  QualType type = CS->getType();
//                int temp = getSizeOfQualType(&type);
//                offset += max(temp, 4);
//            }
        }
        
        for(CXXMethodDecl *VFI : classDecl->methods()) {
            if(VFI->isVirtualAsWritten()) {
                offset+=4;
                break;
            }
        }
        if(classDecl->isUnion()) {
            return 0;

        } else {
            for(const FieldDecl *CS : classDecl->fields()) {
                if(CS->Decl::isFirstDecl() == false)
                    continue;
                if(CS == ND) {
                    found = true;
                    
                    break;
                }
                
                
                
                const  QualType type = CS->getType();
                int temp = getSizeOfQualType(&type);
                offset += max(temp, 4);
            }
        }
        return offset;
        
    }
    

    string GetImm(int size) {
        if((size & 0xFF) == size)
            return "GetImm1 " +  to_string(size);
        else if((size & 0xFFFF) == size)
            return "GetImm2 " +  to_string(size);
        else
            return "GetImm3 " +  to_string(size);
        
    }
    
    string SetImm(int size) {
        if((size & 0xFF) == size)
            return "SetImm1 " +  to_string(size);
        else if((size & 0xFFFF) == size)
            return "SetImm2 " +  to_string(size);
        else
            return "SetImm3 " +  to_string(size);
        
    }

    
    bool parseArraySubscriptExpr(const Expr *e, bool addrOf, bool LValueToRValue = false) {
        const ArraySubscriptExpr *arr = cast<const ArraySubscriptExpr>(e);
        const Expr *base = arr->getBase();
        const Expr *index = arr->getIdx();
        

        parseExpression(index);
        parseExpression(base, true);
        const DeclRefExpr *declRef = getDeclRefExpr(base);
        const Type *type = base->getType().getTypePtr();//declRef->getType().getTypePtr()->getArrayElementTypeNoTypeQual();
        if(type == NULL) {
            type = declRef->getType().getTypePtr();
        }
        if(declRef) {
            declRef->getType();
        }
        if(type->isPointerType())
            type = type->getPointeeType().getTypePtr();
        
        if(LValueToRValue)
             out << "ArrayGet " << getSizeFromBytes(getSizeOfType(type)) << endl;
        else if(addrOf)
            out << "ArrayGetP " << getSizeFromBytes(getSizeOfType(type)) << endl;
        else
            out << "ArraySet " << getSizeFromBytes(getSizeOfType(type)) << endl;
        
        return true;
    }
    
    bool VisitFunctionDecl(FunctionDecl *f) {
        // Only function definitions (with bodies), not declarations.
        int funcNum = 0;
        if (f->hasBody()) {
            if(isa<CXXConstructorDecl>(f))
                return true;
            Stmt *FuncBody = f->getBody();
            
            int paramSize = 0;
            for(int i=0; i<f->getNumParams(); i++) {
                paramSize += getSizeFromBytes(getSizeOfType(f->getParamDecl(i)->getType().getTypePtr()));
            }
            
            out << endl << " //FuncBegin" << endl;
            out << endl << endl << ":@" << f->getBody()->getLocStart().getRawEncoding()  << endl << ":" << dumpName(cast<NamedDecl>(f)) << endl;
            
            string funcString = "Function 1 " + to_string(paramSize + (isa<CXXMethodDecl>(f) ? 1 : 0)) + " " + getNameForFunc(f) + "\n" + "{\n";
            out << funcString;
            
            
            currFunction = f;
            locals.clear();
            if(isa<CXXMethodDecl>(f))
                localInc = 1;
            else
                localInc = 0;
            
            for(uint i=0; i<f->getNumParams(); i++){
                handleParmVarDecl(f->getParamDecl(i));
            }
            localInc += 2;
            parseStatement(FuncBody);
            
            if(f->getReturnType().getTypePtr()->isVoidType()) {
                int paramSize = 0;
                for(int i=0; i<f->getNumParams(); i++) {
                    paramSize += getSizeFromBytes(getSizeOfType(f->getParamDecl(i)->getType().getTypePtr()));
                }
                
                out << "return " << paramSize + (isa<CXXMethodDecl>(f) ? 1 : 0) << " 0" << endl;
            }
            out << "} ";
            out << "#FuncEnd L " << localInc - isa<CXXMethodDecl>(f) << endl << endl;
            
            outfile << out.str();
            out.str(string(""));
            out.clear();
            
        }
        
        return true;
    }
    
    
  
    
    
    uint32_t printVirtualCall(const CXXRecordDecl *classDecl, const CXXMethodDecl *method, Expr *baseExpr, const CXXRecordDecl *superDecl = NULL) {
        int offset = 0;
        
        
        if(superDecl == NULL)
            superDecl = classDecl;
        
        int vtableInc = 0;
        for(auto VBI : classDecl->bases()) {
            
            
            const CXXBaseSpecifier baseSpec = VBI;
            const CXXRecordDecl *baseDecl = baseSpec.getType()->getAsCXXRecordDecl();
            vtableInc += printVirtualCall(baseDecl, method, baseExpr, superDecl);
        }
        
        int func = 0;
        for(CXXMethodDecl *VFI : classDecl->methods()) {
            
            if(VFI->isVirtual()) {
                
                const CXXMethodDecl *VFII = VFI->getCorrespondingMethodInClass(superDecl);
                if(VFI->getName() == method->getName()) { //getLocStart(VFI) != getLocStart(VFII)) {
                    
                    //out << "push " << func << endl;
                    parseExpression(baseExpr);
                    out << endl << "dup" << endl << GetImm(getSizeFromBytes(getSizeOfCXXDecl(superDecl, false, true, classDecl)) + vtableInc) << " //"<< classDecl->getDeclName().getAsString() << "::VTablePtr[" << getSizeFromBytes(getSizeOfCXXDecl(superDecl, false, true, classDecl)) + vtableInc << "]" <<  endl;
                    out << GetImm(func) << " //VTable[" << func << "] //" <<getNameForFunc(method) << endl;
                    out << "pcall" << " //(*)(" << getNameForFunc(method) << "());" << endl;
                    
                    
                }
                    func++;
               // }
                
            }
            
        }
        return getSizeOfVTable(classDecl);
        
        
    }


    
        uint32_t printVTableInit(const CXXRecordDecl *classDecl, const NamedDecl *classLoc) {
            int offset = 0;
            
            
            //string key = classLoc->getDeclName().getAsString();
            int vtableInc = 0;
            for(auto VBI : classDecl->bases()) {
                
                
                const CXXBaseSpecifier baseSpec = VBI;
                const CXXRecordDecl *baseDecl = baseSpec.getType()->getAsCXXRecordDecl();
                //vtableInc += printVTableInit(baseDecl, classLoc);
                bool foundVirt = false;
                int func =0;
                for(CXXMethodDecl *VFI : baseDecl->methods()) {
                    
                    if(VFI->isVirtual()) {
                        if(!foundVirt) {
                            
                            
                            
                            //                        out << "StaticGet 0 //\"this\"" << endl;
                            uint32_t size = getSizeFromBytes(getSizeOfCXXDecl(classDecl, false, false));
                            uint32_t sizeBase = getSizeFromBytes(getSizeOfCXXDecl(classDecl, false, true, baseDecl));
                            out << endl << "//SetVTablePtr" << endl;
                            out << "getFrame1 0" << endl;
                            out << "GetImmp " << size+vtableInc << " //"<< baseDecl->getDeclName().getAsString() << "::VTableStart"  << endl;
                            out << "getFrame1 0" << endl;
                            out <<  SetImm(sizeBase) << " //" <<baseDecl->getDeclName().getAsString() << "::VTablePtr"   << endl;
                            foundVirt = true;
                            out << endl << "//SetVTableFunctionPtrs" << endl;
                        }
                        
                        
                        
                        
                        
                        const CXXMethodDecl *VFII = VFI->getCorrespondingMethodInClass(classDecl);
                        
                        if(VFI != VFII) { //getLocStart(VFI) != getLocStart(VFII)) {
                            const Stmt *body = VFII->FunctionDecl::getBody();
                            
                            out << "PushFunction " << getNameForFunc(VFII) << " // &" << VFII->getDeclName().getAsString() << endl;
                            out << "getFrame1 0" << endl;
                            out << SetImm(getSizeFromBytes(getSizeOfCXXDecl(classDecl, false, false)) + vtableInc +func++) << endl;
                            
                            
                        } else {
                            out <<  "PushFunction " << getNameForFunc(VFII) << " // " << VFII->getDeclName().getAsString() << endl;
                            out << "getFrame1 0" << endl;
                            out << SetImm(getSizeFromBytes(getSizeOfCXXDecl(classDecl, false, false )) + vtableInc +func++) << endl;
                            
                        }
                    }
                    
                }
                if(foundVirt)
                    out << "//EndVTableFunctionPtrs" << endl;
                
                
                
                vtableInc += getSizeOfVTable(baseDecl);
            }
            
        }

    
    string iPush(int64_t val) {
        if(val >= -1 && val <= 7)
            return "iPush " + to_string(val);
        else
            return "iPush " + to_string(val);
    }
    uint64_t getLocStart(const CXXMethodDecl *VFFI) {
        Stmt *body = VFFI->getBody();
        if(body == NULL) {
            body = VFFI->getTemplateInstantiationPattern()->getBody();
        }
        return body->getLocStart().getRawEncoding();
    }
    bool VisitCXXRecordDecl(CXXRecordDecl *d) {
        
        //if(!d->hasBody())
         //   return false;
        //constructors
        for(auto *CS : d->ctors()) {
            if(!CS->hasBody())
                continue;
            localInc = 1;
            locals.clear();
            locals.insert(make_pair(d->getDeclName().getAsString(), 0));
            
            out << endl << endl;
            out << ":" << getLocStart(CS) <<  endl << ":"  << CS->getDeclName().getAsString() << endl <<  "Function 1 " << CS->getNumParams()+1   << " " << getNameForFunc(CS) << endl << "{" << endl;
                currFunction = CS;
            
            for(auto *PI : CS->params()) {
                handleParmVarDecl(PI);
            }
            localInc = (3+CS->getNumParams());
            for(auto *IS : CS->inits()) {

                if(IS->getMember()) {

                    parseExpression(IS->getInit());
                    out << "GetFrame1 0 //\"this\"" << endl;
                    out << SetImm(getSizeFromBytes(getCXXOffsetOfNamedDecl(d, IS->getMember()))) << " //" << IS->getMember()->getDeclName().getAsString() << endl;
                } else {
                    if(isa<CXXConstructExpr>(IS->getInit())) {
                        const CXXConstructExpr *constructor = cast<const CXXConstructExpr>(IS->getInit());
                        for(auto *ARG : constructor->arguments()) {
                            parseExpression(ARG);
                        }
                        out << "GetFrame1 0 //\"this\"" << endl;
                    }
                    parseExpression(IS->getInit(), false, false, false);
                }
            }


            parseStatement(CS->getBody());
            
            int paramSize = 0;
            for(int i=0; i<currFunction->getNumParams(); i++) {
                paramSize += getSizeFromBytes(getSizeOfType(currFunction->getParamDecl(i)->getType().getTypePtr()));
            }
            out << "Return " << paramSize + (isa<CXXMethodDecl>(currFunction)) << " 0" << endl;
            out << "} ";
            out << "#FuncEnd L " << localInc - isa<CXXMethodDecl>(CS) << endl << endl;
            
            if(d->isPolymorphic()) {
                out << endl << endl;
                out << "Function 1 1 @" << d->getNameAsString() << "::VTableInit" << endl << "{" << endl;
                printVTableInit(d, NULL);
                out << "Return 1 0" <<endl;
                out << "} #FuncEnd L 2" << endl;

            }
        }
        return true;
    }

public:
    Rewriter &TheRewriter;
    ASTContext *context;
    stringstream out;
        ofstream outfile;
    const FunctionDecl *currFunction;
};

class GlobalsVisitor : public RecursiveASTVisitor<GlobalsVisitor> {
public:
    GlobalsVisitor(Rewriter &R, ASTContext *context) : TheRewriter(R), context(context) {}
    
    //    bool VisitStmt(Stmt *s) {
    //        // Only care about compound statements.
    //
    //
    //        return true;
    //    }
    //
    
    bool VisitDecl(Decl *D) {
        if(isa<VarDecl>(D)){
            VarDecl *varDecl = cast<VarDecl>(D);
            if(varDecl->hasGlobalStorage()) {
                if(varDecl->getStorageClass() == SC_Static) {
                    if(statics.find(dumpName(cast<NamedDecl>(D))) == statics.end()) {
                        
                        QualType type = varDecl->getType();
                        auto size = getSizeOfQualType(&type );
                        // auto size  = context->getTypeInfoDataSizeInChars(varDecl->getType()).first.getQuantity();
                        
                        
                        statics.insert(make_pair(dumpName(cast<NamedDecl>(D)), staticInc));
                        staticInc+=getSizeFromBytes(size);
                    }

                } else {
                if(globals.find(dumpName(cast<NamedDecl>(D))) == globals.end()) {
                    
                    QualType type = varDecl->getType();
                    auto size = getSizeOfQualType(&type );
                   // auto size  = context->getTypeInfoDataSizeInChars(varDecl->getType()).first.getQuantity();
                    
                    
                    globals.insert(make_pair(dumpName(cast<NamedDecl>(D)), globalInc));
                    globalInc+=getSizeFromBytes(size);
                }
                }
                
            }
        }
        return true;
    }
    
    
    string dumpName(const NamedDecl *ND) {
        if (ND->getDeclName()) {
            
            return ND->getNameAsString();
        }
        return "";
    }
    
    
    
private:
    Rewriter &TheRewriter;
    ASTContext *context;
    };

class LocalsVisitor : public RecursiveASTVisitor<GlobalsVisitor> {
public:
    LocalsVisitor(Rewriter &R, ASTContext *context) : TheRewriter(R), context(context) { currentFunction = NULL; }
    
    //    bool VisitStmt(Stmt *s) {
    //        // Only care about compound statements.
    //
    //
    //        return true;
    //    }
    //
    
    
    
    
    bool VisitDecl(Decl *D) {
        
        if(isa<FunctionDecl>(D)) {
            const FunctionDecl *func = cast<const FunctionDecl>(D);
            if(currentFunction) {
                localCounts.insert(make_pair(currentFunction, localInc - currentFunction->getNumParams() - (isa<CXXMethodDecl>(currentFunction) ? 1 : 0) ));
            }
        }
        return true;
    }
    
    
    
    string dumpName(const NamedDecl *ND) {
        if (ND->getDeclName()) {
            
            return ND->getNameAsString();
        }
        return "";
    }
    
    bool TraverseDecl(Decl *D) {
        RecursiveASTVisitor::TraverseDecl(D);
        if(currentFunction)
            localCounts.insert(make_pair(currentFunction, localInc));
        return true;
    }
    
    
    
private:
    Rewriter &TheRewriter;
    ASTContext *context;
    const FunctionDecl *currentFunction;
    
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(Rewriter &R, ASTContext *context, string filename) : Visitor(R, context, filename), GlobalsVisitor(R, context) {}
    
    // Override the method that gets called for each parsed top-level
    // declaration.
    bool HandleTopLevelDecl(DeclGroupRef DR) override {
        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
            // Traverse the declaration using our AST visitor.
            GlobalsVisitor.TraverseDecl(*b);
//            (*b)->dump();
        }
        
        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
            // Traverse the declaration using our AST visitor.
            Visitor.TraverseDecl(*b);
            //(*b)->dump();
        }

        return true;
    }
    ~MyASTConsumer() {
        Visitor.outfile << "#Statics " << staticInc << endl;
    }
    
private:
    MyASTVisitor Visitor;
    GlobalsVisitor GlobalsVisitor;
    
};



// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
    MyFrontendAction() {}
    void EndSourceFileAction() override {
        SourceManager &SM = TheRewriter.getSourceMgr();
        llvm::errs() << "** EndSourceFileAction for: "
        << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";
        
        // Now emit the rewritten buffer.
        TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
    }
    
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   StringRef file) override {

        llvm::errs() << "** Creating AST consumer for: " << file << "\n";
        TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
                        SourceManager &SM = TheRewriter.getSourceMgr();
        string fileName(string(SM.getFileEntryForID(SM.getMainFileID())->getName()));
        fileName.erase(fileName.find_last_of(".c"));
        
        return llvm::make_unique<MyASTConsumer>(TheRewriter, &CI.getASTContext(), fileName+"asm");
    }
    
private:
    Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
    CommonOptionsParser op(argc, argv, ToolingSampleCategory);
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());
    
    // ClangTool::run accepts a FrontendActionFactory, which is then used to
    // create new objects implementing the FrontendAction interface. Here we use
    // the helper newFrontendActionFactory to create a default factory that will
    // return a new MyFrontendAction object every time.
    // To further customize this, we could create our own factory class.
    return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
