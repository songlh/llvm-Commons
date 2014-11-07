

#ifndef _H_SONGLH_IDMANAGER
#define _H_SONGLH_IDMANAGER


#include "llvm/Pass.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"


using namespace llvm;

namespace llvm_Commons
{

typedef std::vector<Instruction *> InstList;
struct IDManager: public ModulePass {


	static char ID;
	static const unsigned INVALID_ID = (unsigned)-1;

	IDManager();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
	virtual void print(raw_ostream &O, const Module *M) const;

	unsigned size() const { return IDMapping.size(); }
	unsigned getInstructionID(const Instruction *I) const;
	Instruction *getInstruction(unsigned InsID) const;
	InstList getInstructions(unsigned InsID) const;

private:
	DenseMap<unsigned, InstList> IDMapping;
};



}




#endif

