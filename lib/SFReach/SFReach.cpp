#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/AddressUtility.h"

#include "llvm/DebugInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/InstructionSimplify.h"


using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static RegisterPass<StructFieldReach> X(
		"struct-field-reach",
		"reach analysis for struct field",
		false,
		true);


char StructFieldReach::ID = 0;

void StructFieldReach::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesAll();
	AU.addRequired<DataLayout>();
	AU.addRequired<TargetLibraryInfo>();
	AU.addRequired<AliasAnalysis>();
	//AU.addRequired<DominatorTree>();
	//AU.addRequired<LoopInfo>();
	//AU.addRequired<InterPro>();
}

StructFieldReach::StructFieldReach(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeTargetLibraryInfoPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);
	//initializeDominatorTreePass(Registry);
	//initializeLoopInfoPass(Registry);
}

void StructFieldReach::print(raw_ostream &O, const Module *M) const
{
	return;
}

void StructFieldReach::BuildMemFootPrintMapping(Function * pFunction)
{
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			if(isa<LoadInst>(II) || isa<StoreInst>(II) || isa<MemIntrinsic>(II))
			{
				MemFootPrint foot;
				CalMemFootPrint(II, &foot, this->pDL);
				this->InstMemFootPrintMapping[II] = foot;
			}
		}
	}
}

void StructFieldReach::InitBeforeAfterSet(Function * pF)
{
	for(Function::iterator BB = pF->begin(); BB != pF->end(); BB++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			vector<Instruction *> vecPredInst;
			this->InstPredInstVecMapping[II] = vecPredInst;

			vector<Instruction *> vecSuccInst;
			this->InstSuccInstVecMapping[II] = vecSuccInst;

			set<MemFootPrint *> beforeSet;
			this->InstBeforeSetMapping[II] = beforeSet;

			set<MemFootPrint *> afterSet;
			this->InstAfterSetMapping[II] = afterSet;

		}
	}

	for(Function::iterator BB = pF->begin(); BB != pF->end(); BB ++)
	{
		BasicBlock::iterator itFirstInst = BB->begin();

		if(itFirstInst == BB->end() )
		{
			continue;
		}

		for(pred_iterator pred = pred_begin(BB); pred != pred_end(BB); pred++ )
		{
			this->InstPredInstVecMapping[itFirstInst].push_back((*pred)->getTerminator());
		}

		BasicBlock::iterator itLastInst = BB->getTerminator();
		for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++ )
		{
			if((*succ)->begin() == (*succ)->end())
			{
				continue;
			}
			this->InstSuccInstVecMapping[itLastInst].push_back((*succ)->begin());
		}

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			BasicBlock::iterator ITmp;
			if(II != BB->begin())
			{
				ITmp = II;
				ITmp--;
				this->InstPredInstVecMapping[II].push_back(ITmp);
			}

			ITmp = II;
			ITmp ++;

			if(ITmp != BB->end() )
			{
				this->InstSuccInstVecMapping[II].push_back(ITmp);
			}
		}
	}
}


MemRelationKind StructFieldReach::CalMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2)
{
	this->iDebug++;

	if(pPrint1 == pPrint2)
	{
		return MR_IDENTICAL;
	}

	if(pPrint1->pI == pPrint2->pI)
	{
		return MR_IDENTICAL;
	}

	Function * pCurrentFunction = NULL;

	if(pPrint1->pI->getParent()->getParent() == pPrint2->pI->getParent()->getParent() )
	{
		pCurrentFunction = pPrint1->pI->getParent()->getParent();
	}

	if(pCurrentFunction == NULL)
	{
		return MR_UNKNOWN;
	}

//check cache

	pair<MemFootPrint *, MemFootPrint *> PrintPair;
	if(pPrint1 > pPrint2)
	{
		PrintPair.second = pPrint1;
		PrintPair.first = pPrint2;
	}
	else
	{
		PrintPair.first = pPrint1;
		PrintPair.second = pPrint2;
	}

	if(this->FootPrintPairRelationMapping.find(PrintPair) != this->FootPrintPairRelationMapping.end() )
	{
		if(PrintPair.first == pPrint2 )
		{
			if(this->FootPrintPairRelationMapping[PrintPair] == MR_COVER )
			{
				return MR_COVERED;
			}
			else if(this->FootPrintPairRelationMapping[PrintPair] == MR_COVERED)
			{
				return MR_COVER;
			}
		}

		return this->FootPrintPairRelationMapping[PrintPair];
	}

	MemRelationKind kindResult = MR_UNKNOWN;

	//PrintMemFootPrint(pPrint1);
	//PrintMemFootPrint(pPrint2);


	bool bSameObjectCheck = false;
	if(BeSameBaseObject(pPrint1, pPrint2))
	{
		kindResult = CmpMemFootPrintForSameBase(pPrint1, pPrint2);
		bSameObjectCheck = true;
	}

	if(BeDifferentBaseObject(pPrint1, pPrint2, this->pDL))
	{
		//errs() << "different object\n";
		kindResult = MR_NO;
	}

	if(kindResult == MR_UNKNOWN)
	{
		AliasAnalysis::AliasResult aliasResult = this->pAA->alias(pPrint1->pBaseObject, 1, pPrint2->pBaseObject, 1);
		if(aliasResult == AliasAnalysis::NoAlias)
		{
			//errs() << "no alias\n";
			kindResult = MR_NO;
		}
		else if(aliasResult == AliasAnalysis::MustAlias && !bSameObjectCheck)
		{
			kindResult = CmpMemFootPrintForSameBase(pPrint1, pPrint2);
			bSameObjectCheck = true;
		}
	}

	if(kindResult == MR_UNKNOWN)
	{
		AliasAnalysis::AliasResult aliasResult = this->pAA->alias(pPrint1->pPointer, pPrint1->uLength, pPrint2->pPointer, pPrint2->uLength);

		if(aliasResult == AliasAnalysis::MustAlias)
		{
			if(pPrint1->uLength == UnknownSize || pPrint2->uLength == UnknownSize)
			{
				kindResult = MR_OVERLAP;
			}
			else
			{
				if(pPrint1->uLength == pPrint2->uLength)
				{
					kindResult = MR_IDENTICAL;
				}
				else if(pPrint1->uLength < pPrint2->uLength)
				{
					kindResult = MR_COVERED;
				}
				else
				{
					kindResult = MR_COVER;
				}
			}

		}
		else if(aliasResult == AliasAnalysis::NoAlias)
		{
			kindResult = MR_NO;
		
		}
		else if(aliasResult == AliasAnalysis::PartialAlias)
		{
			kindResult = MR_OVERLAP;
		}
		else
		{
			kindResult = MR_UNKNOWN;
		}

	}

	if(kindResult == MR_UNKNOWN && bSameObjectCheck)
	{
		if(pPrint1->uOffset == pPrint2->uOffset)
		{
			if(pPrint1->uLength != UnknownSize && pPrint1->uMaxLength != UnknownSize && pPrint2->uLength != UnknownSize && pPrint2->uMaxLength != UnknownSize)
			{
				kindResult = MR_OVERLAP;
			}
		}
	}

//update cache
	if(PrintPair.first == pPrint2 )
	{
		if(kindResult == MR_COVER)
		{
			this->FootPrintPairRelationMapping[PrintPair] = MR_COVERED;
		}
		else if(kindResult == MR_COVERED)
		{
			this->FootPrintPairRelationMapping[PrintPair] = MR_COVER;
		}
		else
		{
			this->FootPrintPairRelationMapping[PrintPair] = kindResult;
		}
	}
	else
	{
		this->FootPrintPairRelationMapping[PrintPair] = kindResult;
	}

	return kindResult;


}

void StructFieldReach::AssignID()
{
	map<Instruction*, MemFootPrint>::iterator itInstPrintBegin = this->InstMemFootPrintMapping.begin();
	map<Instruction*, MemFootPrint>::iterator itInstPrintEnd = this->InstMemFootPrintMapping.end();

	int iCurrent = 0;

	for(; itInstPrintBegin != itInstPrintEnd; itInstPrintBegin++)
	{
		this->MemFootPrintIDMapping[&(itInstPrintBegin->second)] = iCurrent;
		this->IDMemFootPrintMapping[iCurrent] = &(itInstPrintBegin->second);

		iCurrent ++;
	}
}

void StructFieldReach::DumpMemFootPrint()
{
	map<int, MemFootPrint *>::iterator itIDPrintBegin = this->IDMemFootPrintMapping.begin();
	map<int, MemFootPrint *>::iterator itIDPrintEnd = this->IDMemFootPrintMapping.end();

	for(; itIDPrintBegin != itIDPrintEnd ; itIDPrintBegin ++)
	{
		errs() << itIDPrintBegin->first << "\n";
		PrintMemFootPrint(itIDPrintBegin->second);
	}
}

void StructFieldReach::DumpCachedRelation()
{

	errs() << this->FootPrintPairRelationMapping.size() << "\n";

	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapBegin = this->FootPrintPairRelationMapping.begin();
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapEnd = this->FootPrintPairRelationMapping.end();

	int iIdentical = 0;
	int iCover = 0;
	int iCovered = 0;
	int iOverlap = 0;
	int iNo = 0;
	int iUnknown = 0;

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second == MR_IDENTICAL)
		{	
			iIdentical += 1;
		}
		else if(itMapBegin->second == MR_COVER)
		{
			iCover += 1;
		}
		else if(itMapBegin->second == MR_COVERED)
		{
			iCovered +=1;
		}
		else if(itMapBegin->second == MR_OVERLAP)
		{
			iOverlap += 1;
		}
		else if(itMapBegin->second == MR_NO)
		{
			iNo += 1;
		}
		else
		{
			iUnknown += 1;
		}
	}

	errs() << "MR_IDENTICAL: " << iIdentical << "\n";
	errs() << "MR_COVER: " << iCover << "\n";
	errs() << "MR_COVERED: " << iCovered << "\n";
	errs() << "MR_OVERLAP: " << iOverlap << "\n";
	errs() << "MR_NO: " << iNo << "\n";
	errs() << "MR_UNKNOWN: " << iUnknown << "\n";

	//return;
	itMapBegin = this->FootPrintPairRelationMapping.begin();

	//int iCount = 0;
	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second != MR_NO )
		{
			continue;
		}

		//if(iCount > 40 && iCount <= 61 )
		//{
			errs() << this->MemFootPrintIDMapping[itMapBegin->first.first] << "\n";
			PrintMemFootPrint(itMapBegin->first.first);

			errs() << this->MemFootPrintIDMapping[itMapBegin->first.second] << "\n";
			PrintMemFootPrint(itMapBegin->first.second);

			errs() << "**************************************************************************************\n";
			
		//}
		//iCount ++;


	}




}




void StructFieldReach::CalAfterSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent )
{
	afterSet.clear();

	set<MemFootPrint *>::iterator itSetFootBegin = beforeSet.begin();
	set<MemFootPrint *>::iterator itSetFootEnd = beforeSet.end();

	if(isa<StoreInst>(pCurrent) || isa<MemIntrinsic>(pCurrent))
	{

		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			MemRelationKind resultKind = CalMemWriteRelation(&(this->InstMemFootPrintMapping[pCurrent]), *itSetFootBegin);

			if(!(resultKind == MR_IDENTICAL || resultKind == MR_COVER))
			{
				afterSet.insert(*itSetFootBegin);
			}
		}

		afterSet.insert( &(this->InstMemFootPrintMapping[pCurrent]) );
	}
	else
	{	
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			afterSet.insert(*itSetFootBegin);
		}
	}
}



void StructFieldReach::IntraFieldReachAnalysis(Function * pF)
{
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstBegin = this->InstBeforeSetMapping.begin();
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstEnd = this->InstBeforeSetMapping.end();

	vector<Instruction *> vecWorkList;

	for(; itMapInstBegin != itMapInstEnd; itMapInstBegin++ )
	{
		vecWorkList.push_back(itMapInstBegin->first);
	}

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		vector<Instruction *>::iterator itPredInstVecBegin = this->InstPredInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itPredInstVecEnd = this->InstPredInstVecMapping[pCurrent].end();

		this->InstBeforeSetMapping[pCurrent].clear();

		for(; itPredInstVecBegin != itPredInstVecEnd; itPredInstVecBegin ++ )
		{
			set<MemFootPrint *>::iterator itAfterSetBegin = this->InstAfterSetMapping[*itPredInstVecBegin].begin();
			set<MemFootPrint *>::iterator itAfterSetEnd = this->InstAfterSetMapping[*itPredInstVecBegin].end();

			for(; itAfterSetBegin != itAfterSetEnd; itAfterSetBegin ++ )
			{
				this->InstBeforeSetMapping[pCurrent].insert(*itAfterSetBegin);
			}
		}

		set<MemFootPrint *> afterSet;

		CalAfterSet(this->InstBeforeSetMapping[pCurrent], afterSet, pCurrent);

		if(CmpMemFootPrintSet(this->InstAfterSetMapping[pCurrent], afterSet))
		{
			continue;
		}

		this->InstAfterSetMapping[pCurrent] = afterSet;

		vector<Instruction *>::iterator itSuccInstVecBegin = this->InstSuccInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itSuccInstVecEnd = this->InstSuccInstVecMapping[pCurrent].end();

		for(; itSuccInstVecBegin != itSuccInstVecEnd; itSuccInstVecBegin ++ )
		{
			vecWorkList.push_back(*itSuccInstVecBegin);
		}

	}

}


void StructFieldReach::DumpRetBefore(Function * pFunction)
{
	ReturnInst * pRet = NULL;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(ReturnInst * pR = dyn_cast<ReturnInst>(II))
			{
				pRet = pR;
			}
		}
	}

	errs() << this->InstBeforeSetMapping[pRet].size() << "\n";
}


void StructFieldReach::TestDriver(Module & M)
{
	Function * pFunction = M.getFunction("synth_mult");

	BuildMemFootPrintMapping(pFunction);
	InitBeforeAfterSet(pFunction);
	AssignID();

	//DumpMemFootPrint();
	IntraFieldReachAnalysis(pFunction);
	DumpRetBefore(pFunction);
	//DumpCachedRelation();
	
}




bool StructFieldReach::runOnModule(Module& M)
{
	//this->pBasicAA = &getAnalysis<BasicAA>();
	this->pAA = &getAnalysis<AliasAnalysis>();
	this->pDL = &getAnalysis<DataLayout>();
	this->pTLI = &getAnalysis<TargetLibraryInfo>();
	//this->pInterPro = &getAnalysis<InterPro>();

	this->iDebug = 0;
	//TestDriver(&M);
	TestDriver(M);
	



	return false;
}

