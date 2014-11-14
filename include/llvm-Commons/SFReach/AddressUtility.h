


#include "SFReach.h"


using namespace std;
using namespace llvm;

namespace llvm_Commons
{

bool BeValuePropagation(Instruction *, Value *);
bool BeSameBaseObject(MemFootPrint *, MemFootPrint *);
bool BeDifferentType(Type *, Type *);
bool BeDifferentBaseObject(MemFootPrint *, MemFootPrint *, DataLayout * pDL);


bool BeLocalObject(Value *);
bool BeInputObject(Value *);

void CalMemFootPrint(Instruction *, MemFootPrint *, DataLayout * pDL );
void PrintMemFootPrint(MemFootPrint * pFoot);
bool CmpMemFootPrintSet( set<MemFootPrint *> & SA, set<MemFootPrint *> & SB );

MemRelationKind CmpMemFootPrintForSameBase(MemFootPrint * , MemFootPrint *);

}


