#include "llvm-Commons/ID/IDManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Constants.h"


using namespace llvm_Commons;

static RegisterPass<IDManager> X("manage-id",
                                 "Find the instruction with a particular ID; "
                                 "Lookup the ID of an instruction",
                                 false, true);

char IDManager::ID = 0;

void IDManager::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesAll();
}

IDManager::IDManager(): ModulePass(ID) {}

bool IDManager::runOnModule(Module &M) {
	IDMapping.clear();
	for (Module::iterator F = M.begin(); F != M.end(); ++F) {
		for (Function::iterator B = F->begin(); B != F->end(); ++B) {
			for (BasicBlock::iterator I = B->begin(); I != B->end(); ++I) {
				unsigned InsID = getInstructionID(I);
				if (InsID != INVALID_ID)
					IDMapping[InsID].push_back(I);
			}
		}
	}

	if (size() == 0)
		errs() << "[Warning] No ID information in this program.\n";

	return false;
}

unsigned IDManager::getInstructionID(const Instruction *I) const {
	MDNode *Node = I->getMetadata("ins_id");
	if (!Node)
		return INVALID_ID;
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
	assert(CI);
	return CI->getZExtValue();
}

Instruction *IDManager::getInstruction(unsigned InsID) const {
	InstList Insts = getInstructions(InsID);
	if (Insts.size() == 0 || Insts.size() > 1)
		return NULL;
	else
		return Insts[0];
}

InstList IDManager::getInstructions(unsigned InsID) const {
	return IDMapping.lookup(InsID);
}

void IDManager::print(raw_ostream &O, const Module *M) const {

}

