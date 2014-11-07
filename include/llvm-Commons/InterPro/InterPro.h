#ifndef _H_SONGLH_INTERPRO
#define _H_SONGLH_INTERPRO

#include <set>
#include <map>

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"


using namespace llvm;
using namespace std;




namespace llvm_Commons {

struct InterPro: public ModulePass
{
	static char ID;
	InterPro();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;
	virtual void print(raw_ostream &O,  Module *M) ;


public:
	void visit(Module & M);
	void visit(Function * pFunction);


private:
	map<Instruction *, set< Instruction * > > InstBeforeSetMapping;
	map<Instruction *, set< Instruction * > > InstAfterSetMapping;



};




}




#endif

