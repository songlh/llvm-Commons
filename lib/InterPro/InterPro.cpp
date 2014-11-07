

#include <map>

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/DebugInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CallSite.h"
#include "llvm/IR/IntrinsicInst.h"

using namespace std;
using namespace llvm;

#include "llvm-Commons/InterPro/InterPro.h"
using namespace llvm_Commons;

static RegisterPass<InterPro> X(
    "build-inst-baset",
    "build before and after instruction set",
    false,
    true);

static cl::opt<bool> PrintSetSize("print-set-num",
                                cl::desc("Print the size of before and after set"));

char InterPro::ID = 0;

void InterPro::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesAll();
}

InterPro::InterPro(): ModulePass(ID) {}


void InterPro::visit( Module & M)
{

	//Function * pMain = M.getFunction("main");
	this->InstBeforeSetMapping.clear();
	this->InstAfterSetMapping.clear();

	map<Function *, set<Instruction *> > FunctionRetSiteMapping;
	map<Function *, set<ReturnInst *> > FunctionRetMapping; 

	for(Module::iterator F = M.begin(); F != M.end(); F ++ )
	{
		if(FunctionRetMapping.find(F) == FunctionRetMapping.end())
		{
			set<ReturnInst *> setReturn;
			FunctionRetMapping[F] = setReturn;

			set<Instruction *> setRetSite;
			FunctionRetSiteMapping[F] = setRetSite;
		}

		for(Function::iterator BB = F->begin(); BB != F->end(); ++ BB)
		{
			for(BasicBlock::iterator I = BB->begin(); I != BB->end(); ++ I)
			{
				if(ReturnInst * pRet = dyn_cast<ReturnInst>(I))
				{
					FunctionRetMapping[F].insert(pRet);
				}

				if(this->InstBeforeSetMapping.find(I) == this->InstBeforeSetMapping.end())
				{
					set<Instruction *> setBefore;
					this->InstBeforeSetMapping[I] = setBefore;
				}

				if(this->InstAfterSetMapping.find(I) == this->InstAfterSetMapping.end() )
				{
					set<Instruction *> setAfter;
					this->InstAfterSetMapping[I] = setAfter;
				}
			}

		}
	}


	for(Module::iterator F = M.begin(); F != M.end(); F ++)
	{
		for(Function::iterator BB = F->begin(); BB != F->end(); ++ BB)
		{
			Instruction * InstFirst = BB->begin();

			if(InstFirst == BB->end() )
			{
				continue;
			}

			for(pred_iterator pred = pred_begin(BB); pred != pred_end(BB); pred++ )
			{
				Instruction * term = (*pred)->getTerminator();

				if(isa<CallInst>(term) || isa<InvokeInst>(term))
				{
					CallSite cs = CallSite(term);
					Function * pCalledFunction = cs.getCalledFunction();
					if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
					{
						this->InstBeforeSetMapping[InstFirst].insert(term);
					}
					else
					{
						FunctionRetSiteMapping[pCalledFunction].insert(InstFirst);
					}
				}
				else
				{
					this->InstBeforeSetMapping[InstFirst].insert(term);	
				}

			}

			Instruction * InstLast = BB->getTerminator();

			if(isa<CallInst>(InstLast) || isa<InvokeInst>(InstLast))
			{
				CallSite cs = CallSite(InstLast);
				Function * pCalledFunction = cs.getCalledFunction();
				if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
				{
					for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++)
					{	
						this->InstAfterSetMapping[InstLast].insert((*succ)->begin());
					}
				}
				else
				{
					assert(pCalledFunction->begin() != pCalledFunction->end());
					assert(pCalledFunction->begin()->begin() != pCalledFunction->begin()->end());

					this->InstAfterSetMapping[InstLast].insert(pCalledFunction->begin()->begin());
					this->InstBeforeSetMapping[pCalledFunction->begin()->begin()].insert(InstLast);	
				}
			}
			else
			{
				for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++)
				{	
					this->InstAfterSetMapping[InstLast].insert((*succ)->begin());
				}

			}

			for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I ++)
			{
				if(isa<CallInst>(I) || isa<InvokeInst>(I))
				{
					CallSite cs = CallSite(I);
					Function * pCalledFunction = cs.getCalledFunction();
					if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
					{
						BasicBlock::iterator next = I;
						next++;	
						if(next != BB->end() )
						{
							this->InstAfterSetMapping[I].insert(next);
						}
					}
					else
					{
						assert(pCalledFunction->begin() != pCalledFunction->end());
						assert(pCalledFunction->begin()->begin() != pCalledFunction->begin()->end());

						this->InstAfterSetMapping[I].insert(pCalledFunction->begin()->begin());
						this->InstBeforeSetMapping[pCalledFunction->begin()->begin()].insert(I);
					}

				}
				else
				{
					BasicBlock::iterator next = I;
					next ++;

					if(next != BB->end())
					{
						this->InstAfterSetMapping[I].insert(next);
					}
				}

				BasicBlock::iterator previous = I;

				if(previous != BB->begin() )
				{
					previous --;

					if(isa<CallInst>(previous) || isa<InvokeInst>(previous))
					{

						CallSite cs = CallSite(previous);
						Function * pCalledFunction = cs.getCalledFunction();
						if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
						{
							this->InstBeforeSetMapping[I].insert(previous);
						}
						else
						{
							FunctionRetSiteMapping[pCalledFunction].insert(I);
						}

					}
					else
					{
						this->InstBeforeSetMapping[I].insert(previous);
					}
				}
			}
		}	
	}


	map<Function *, set<Instruction *> >::iterator itMapFuncBegin = FunctionRetSiteMapping.begin();
	map<Function *, set<Instruction *> >::iterator itMapFuncEnd = FunctionRetSiteMapping.end();

	for(; itMapFuncBegin != itMapFuncEnd ; itMapFuncBegin++ )
	{

		set<Instruction *>::iterator itSetInstBegin = itMapFuncBegin->second.begin();
		set<Instruction *>::iterator itSetInstEnd = itMapFuncBegin->second.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{
			set<ReturnInst *>::iterator itRetInstBegin = FunctionRetMapping[itMapFuncBegin->first].begin();
			set<ReturnInst *>::iterator itRetInstEnd = FunctionRetMapping[itMapFuncBegin->first].end();

			for(;itRetInstBegin != itRetInstEnd; itRetInstBegin ++)
			{
				this->InstBeforeSetMapping[*itSetInstBegin].insert(*itRetInstBegin);
				this->InstAfterSetMapping[*itRetInstBegin].insert(*itSetInstBegin);
			}
		}
	}
}


void InterPro::visit(Function * pFunction )
{
	this->InstBeforeSetMapping.clear();
	this->InstAfterSetMapping.clear();

	map<Function *, set<Instruction *> > FunctionRetSiteMapping;
	map<Function *, set<ReturnInst *> > FunctionRetMapping; 

	vector<Function *> vecWorkList;
	set<Function *> setProcessFunction;

	if(FunctionRetMapping.find(pFunction) == FunctionRetMapping.end())
	{
		set<ReturnInst *> setReturn;
		FunctionRetMapping[pFunction] = setReturn;

		set<Instruction *> setRetSite;
		FunctionRetSiteMapping[pFunction] = setRetSite;
	}

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); ++ BB)
	{
		for(BasicBlock::iterator I = BB->begin(); I != BB->end(); ++ I)
		{
			if(ReturnInst * pRet = dyn_cast<ReturnInst>(I))
			{
				FunctionRetMapping[pFunction].insert(pRet);
			}

			if(isa<CallInst>(I) || isa<InvokeInst>(I))
			{
				CallSite cs = CallSite(I);
				Function * pCalledFunction = cs.getCalledFunction();
				if(pCalledFunction != NULL && !pCalledFunction->isDeclaration() )
				{
					if(setProcessFunction.find(pCalledFunction) == setProcessFunction.end() )
					{	
						setProcessFunction.insert(pCalledFunction);
						vecWorkList.push_back(pCalledFunction);
					}
				}
			}

			if(this->InstBeforeSetMapping.find(I) == this->InstBeforeSetMapping.end())
			{
				set<Instruction *> setBefore;
				this->InstBeforeSetMapping[I] = setBefore;
			}

			if(this->InstAfterSetMapping.find(I) == this->InstAfterSetMapping.end() )
			{
				set<Instruction *> setAfter;
				this->InstAfterSetMapping[I] = setAfter;
			}
		}
	}

	while(vecWorkList.size() > 0)
	{
		Function * pF = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		if(FunctionRetMapping.find(pF) == FunctionRetMapping.end() )
		{
			set<ReturnInst *> setReturn;
			FunctionRetMapping[pF] = setReturn;

			set<Instruction *> setRetSite;
			FunctionRetSiteMapping[pF] = setRetSite;
		}

		for(Function::iterator BB = pF->begin(); BB != pF->end(); ++BB)
		{
			for(BasicBlock::iterator I = BB->begin(); I != BB->end(); ++ I)
			{
				if(ReturnInst * pRet = dyn_cast<ReturnInst>(I))
				{
					FunctionRetMapping[pF].insert(pRet);
				}

				if(isa<CallInst>(I) || isa<InvokeInst>(I))
				{
					CallSite cs = CallSite(I);
					Function * pCalledFunction = cs.getCalledFunction();
					if(pCalledFunction != NULL && !pCalledFunction->isDeclaration() )
					{
						if(setProcessFunction.find(pCalledFunction) == setProcessFunction.end())
						{
							setProcessFunction.insert(pCalledFunction);
							vecWorkList.push_back(pCalledFunction);
						}
					}
				}

				if(this->InstBeforeSetMapping.find(I) == this->InstBeforeSetMapping.end())
				{
					set<Instruction *> setBefore;
					this->InstBeforeSetMapping[I] = setBefore;
				}

				if(this->InstAfterSetMapping.find(I) == this->InstAfterSetMapping.end() )
				{
					set<Instruction *> setAfter;
					this->InstAfterSetMapping[I] = setAfter;
				}
			}
		}
	}	

	set<Function *>::iterator itSetFuncBegin = setProcessFunction.begin();
	set<Function *>::iterator itSetFuncEnd = setProcessFunction.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin++ )
	{

		Function * pF = *itSetFuncBegin;
		for(Function::iterator BB = pF->begin(); BB != pF->end(); ++ BB)
		{
			Instruction * InstFirst = BB->begin();

			if(InstFirst == BB->end() )
			{
				continue;
			}

			for(pred_iterator pred = pred_begin(BB); pred != pred_end(BB); pred++ )
			{
				Instruction * term = (*pred)->getTerminator();

				if(isa<CallInst>(term) || isa<InvokeInst>(term))
				{
					CallSite cs = CallSite(term);
					Function * pCalledFunction = cs.getCalledFunction();
					if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
					{
						this->InstBeforeSetMapping[InstFirst].insert(term);
					}
					else
					{
						FunctionRetSiteMapping[pCalledFunction].insert(InstFirst);
					}
				}
				else
				{
					this->InstBeforeSetMapping[InstFirst].insert(term);	
				}
			}

			Instruction * InstLast = BB->getTerminator();

			if(isa<CallInst>(InstLast) || isa<InvokeInst>(InstLast))
			{
				CallSite cs = CallSite(InstLast);
				Function * pCalledFunction = cs.getCalledFunction();
				if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
				{
					for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++)
					{	
						this->InstAfterSetMapping[InstLast].insert((*succ)->begin());
					}
				}
				else
				{
					assert(pCalledFunction->begin() != pCalledFunction->end());
					assert(pCalledFunction->begin()->begin() != pCalledFunction->begin()->end());

					this->InstAfterSetMapping[InstLast].insert(pCalledFunction->begin()->begin());
					this->InstBeforeSetMapping[pCalledFunction->begin()->begin()].insert(InstLast);	
				}
			}
			else
			{
				for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++)
				{	
					this->InstAfterSetMapping[InstLast].insert((*succ)->begin());
				}
			}

			for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I ++)
			{
				if(isa<CallInst>(I) || isa<InvokeInst>(I))
				{
					CallSite cs = CallSite(I);
					Function * pCalledFunction = cs.getCalledFunction();
					if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
					{
						BasicBlock::iterator next = I;
						next++;	
						if(next != BB->end() )
						{
							this->InstAfterSetMapping[I].insert(next);
						}
					}
					else
					{
						assert(pCalledFunction->begin() != pCalledFunction->end());
						assert(pCalledFunction->begin()->begin() != pCalledFunction->begin()->end());

						this->InstAfterSetMapping[I].insert(pCalledFunction->begin()->begin());
						this->InstBeforeSetMapping[pCalledFunction->begin()->begin()].insert(I);
					}

				}
				else
				{
					BasicBlock::iterator next = I;
					next ++;

					if(next != BB->end())
					{
						this->InstAfterSetMapping[I].insert(next);
					}
				}

				BasicBlock::iterator previous = I;

				if(previous != BB->begin() )
				{
					previous --;

					if(isa<CallInst>(previous) || isa<InvokeInst>(previous))
					{

						CallSite cs = CallSite(previous);
						Function * pCalledFunction = cs.getCalledFunction();
						if(pCalledFunction == NULL || pCalledFunction->isDeclaration() )
						{
							this->InstBeforeSetMapping[I].insert(previous);
						}
						else
						{
							FunctionRetSiteMapping[pCalledFunction].insert(I);
						}

					}
					else
					{
						this->InstBeforeSetMapping[I].insert(previous);
					}
				}
			}
		}

	}

	map<Function *, set<Instruction *> >::iterator itMapFuncBegin = FunctionRetSiteMapping.begin();
	map<Function *, set<Instruction *> >::iterator itMapFuncEnd = FunctionRetSiteMapping.end();

	for(; itMapFuncBegin != itMapFuncEnd ; itMapFuncBegin++ )
	{

		set<Instruction *>::iterator itSetInstBegin = itMapFuncBegin->second.begin();
		set<Instruction *>::iterator itSetInstEnd = itMapFuncBegin->second.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{
			set<ReturnInst *>::iterator itRetInstBegin = FunctionRetMapping[itMapFuncBegin->first].begin();
			set<ReturnInst *>::iterator itRetInstEnd = FunctionRetMapping[itMapFuncBegin->first].end();

			for(;itRetInstBegin != itRetInstEnd; itRetInstBegin ++)
			{
				this->InstBeforeSetMapping[*itSetInstBegin].insert(*itRetInstBegin);
				this->InstAfterSetMapping[*itRetInstBegin].insert(*itSetInstBegin);
			}
		}
	}



}



bool InterPro::runOnModule(Module &M) {

	if(PrintSetSize)
	{
		Function * pFunction = M.getFunction("test2");
		visit(pFunction);
		print(errs(), &M);
	}

	return false;

}

void InterPro::print(raw_ostream &O, const Module *M) const
{
	return;
}

void InterPro::print(raw_ostream &O,  Module *M)  
{

	char pPath[100];
	for(Module::iterator F = M->begin(); F != M->end(); F ++)
	{
		if(!F->getName().startswith("test"))
		{
			continue;
		}

		O << F->getName() << ":\n";

		for(Function::iterator BB = F->begin(); BB != F->end(); ++ BB)
		{
			for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I ++)
			{
				I->dump();

				if( MDNode *N = I->getMetadata("dbg") )
				{	 
					DILocation Loc(N);
					string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
					realpath( sFileNameForInstruction.c_str() , pPath);
					sFileNameForInstruction = string(pPath);                        
					unsigned int uLineNoForInstruction = Loc.getLineNumber();
					O << sFileNameForInstruction << ": " << uLineNoForInstruction << ": ";
				}

				O << this->InstBeforeSetMapping[I].size() << " ";
				O << this->InstAfterSetMapping[I].size() << "\n";
			}

		}


		O << "*********************************************\n";

	}
	
}


