#ifndef _H_SONGLH_SFREACHABILITY
#define _H_SONGLH_SFREACHABILITY

#include <vector>
#include <map>
#include <set>

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Target/TargetLibraryInfo.h"




using namespace llvm;
using namespace std;





namespace llvm_Commons
{

static uint64_t const UnknownSize = ~UINT64_C(0);

enum ExtensionKind {
	EK_NotExtended,
	EK_SignExt,
	EK_ZeroExt
};


struct VariableGEPIndex {
	const llvm::Value *V;
	ExtensionKind Extension;
	int64_t Scale;

	bool operator==(const VariableGEPIndex &Other) const {
		return V == Other.V && Extension == Other.Extension &&
		Scale == Other.Scale;
	}

	bool operator!=(const VariableGEPIndex &Other) const {
		return !operator==(Other);
	}
};

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
	Instruction * pI;
	Value * pBaseObject;
	Value * pPointer;
	Value * pLength;
	uint64_t uLength;
	Value * pOffset;
	uint64_t uOffset;
	uint64_t uMaxLength;
	SmallVector<VariableGEPIndex, 4> GEPVariableIndices;
	bool bInput;
	bool bLocal;
	set<Type *> setSubTypes;

} MemFootPrint;




struct StructFieldReach : public ModulePass
{
	static char ID;
	StructFieldReach();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;

private:
	void InitBeforeAfterSet(Function * pF);
	void BuildMemFootPrintMapping(Function * pFunction);
	MemRelationKind CalMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2);
	void CalAfterSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent );
	void IntraFieldReachAnalysis(Function * pF);

	void DumpRetBefore(Function * pFunction);

	void TestDriver(Module & M);
	void AssignID();
	void DumpMemFootPrint();
	void DumpCachedRelation();

private:
	int iDebug;
	map<Instruction *, vector< Instruction *> > InstPredInstVecMapping;
	map<Instruction *, vector< Instruction *> > InstSuccInstVecMapping;

	map<Instruction *, set< MemFootPrint *> > InstBeforeSetMapping;
	map<Instruction *, set< MemFootPrint *> > InstAfterSetMapping;

	map<Instruction*, MemFootPrint> InstMemFootPrintMapping;
	map<MemFootPrint *, int> MemFootPrintIDMapping;
	map<int, MemFootPrint *> IDMemFootPrintMapping;


	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind> FootPrintPairRelationMapping;


	AliasAnalysis * pAA;
	DataLayout * pDL;
	TargetLibraryInfo * pTLI;


};

}




#endif

