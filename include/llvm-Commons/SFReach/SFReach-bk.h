#ifndef _H_SONGLH_SFREACHABILITY
#define _H_SONGLH_SFREACHABILITY


#include <vector>
#include <map>
#include <set>

#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Target/TargetLibraryInfo.h"


//#include "llvm-Commons/BasicAA/BasicAA.h"
#include "llvm-Commons/InterPro/InterPro.h"

using namespace llvm;
using namespace std;

namespace llvm_Commons
{

enum MemRelationKind
{
	MR_NO,
	MR_OVERLAP,
	MR_IDENTICAL,
	MR_COVER,
	MR_COVERED,
	MR_UNKNOWN
};

typedef struct stMemFootPrint
{
	Value * pointer;
	Value * pLength;
	unsigned uLength;
	unsigned uMax;
} MemFootPrint;


struct StructFieldReach : public ModulePass 
{
	static char ID;
	StructFieldReach();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;

private:
	void TestDriver( Module * pM );
	void AliasTestDriver(Module *pM);


	MemRelationKind CalMemWriteRelationFromSameBaseObject(Instruction * IA, MemFootPrint * Print1, Instruction * IB ,  MemFootPrint * Print2);
	MemRelationKind CalMemWriteRelation(Instruction * IA, Instruction * IB);

	void CalAfterSet(set<Instruction *> & beforeSet, set<Instruction *> & afterSet, Instruction * pCurrent);
	void CalExtendAfterSet( set<pair<Instruction *, Value * > > & , set<pair<Instruction *, Value * > > &, Instruction *, vector<pair<Instruction *, Argument *> > & );


	void InitBeforeAfterSet(Function * pF);
	void IntraFieldReachAnalysis(Function * pFunction);
	void InterFieldReachAnalysis(Function * pFunction);




private:
	map<Instruction *, vector< Instruction *> > InstPredInstVecMapping;
	map<Instruction *, vector< Instruction *> > InstSuccInstVecMapping;


	map<Instruction *, set< Instruction *> > InstBeforeSetMapping;
	map<Instruction *, set< Instruction *> > InstAfterSetMapping;


	map<Instruction *, set< pair<Instruction *, Value * > > > InstExtendBeforeSetMapping;
	map<Instruction *, set< pair<Instruction *, Value * > > > InstExtendAfterSetMapping;

	map<CallSite, set< pair<Instruction *, Value *> > > CallLivePairSetMapping;



	map<pair<Instruction *, Instruction *>, MemRelationKind> InstPairRelationMapping;



	//BasicAA * pBasicAA;
	AliasAnalysis * pAA;
	DataLayout * pDL;
	TargetLibraryInfo * pTLI;
	InterPro * pInterPro;



	DominatorTree * pDT;
	LoopInfo * pLI;
	
};



}




#endif

