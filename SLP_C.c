/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"

/* Header file global to this project */
#include "cfg.h"
#include "loop.h"
#include "worklist.h"
#include "valmap.h"


// dom:  does a dom b?
//
//       a and b can be instructions. This is different
//       from the LLVMDominates API which requires basic
//       blocks.



  int array[7] = {0};

static int dom(LLVMValueRef a, LLVMValueRef b)
{
  if (LLVMGetInstructionParent(a)!=LLVMGetInstructionParent(b)) {
    LLVMValueRef fun = LLVMGetBasicBlockParent(LLVMGetInstructionParent(a));
    // a dom b?
    return LLVMDominates(fun,LLVMGetInstructionParent(a),
			 LLVMGetInstructionParent(b));
  }

  // a and b must be in same block
  // which one comes first?
  LLVMValueRef t = a;
  while(t!=NULL) {
    if (t==b)
      return 1;
    t = LLVMGetNextInstruction(t);
  }
  return 0;
}



static LLVMBuilderRef Builder;

typedef struct VectorPairDef {
  LLVMValueRef pair[2];
  int insertAt0;
  struct VectorPairDef *next;
  struct VectorPairDef *prev;
} VectorPair;

typedef struct  {
  VectorPair *head;
  VectorPair *tail;
  valmap_t    visited;
  valmap_t    sliceA;
  int size;  
  int score;
} VectorList;

static VectorList* VectorList_Create() {
  VectorList *new = (VectorList*) malloc(sizeof(VectorList));
  new->head = NULL;
  new->tail = NULL;
  new->visited = valmap_create();
  new->sliceA = valmap_create();
  new->size=0;
  return new;
}

static void VectorList_Destroy(VectorList *list)
{
  valmap_destroy(list->visited);
  valmap_destroy(list->sliceA);
  VectorPair *head = list->head;
  VectorPair *tmp;
  while(head) {
    tmp = head;
    head=head->next;
    free(tmp);    
  }
  free(list);
}

//
// add a and b to the current chain of vectorizable instructions
//
static VectorPair *VectorList_AppendPair(VectorList *list, LLVMValueRef a, LLVMValueRef b)
{
  VectorPair *new = (VectorPair*) malloc(sizeof(VectorPair));
  new->pair[0] = a;
  new->pair[1] = b;
  new->insertAt0 = 1;
  valmap_insert(list->visited,a,(void*)1);
  valmap_insert(list->visited,b,(void*)1);
  new->next = NULL;
  new->prev = NULL;
  // insert at head
  if (list->head==NULL) {
    list->head = new;
    list->tail = new;
  } else {
    // find right place to insert
    VectorPair *temp = list->head;
    VectorPair *prev = NULL;

    while(temp && dom(temp->pair[0],a)) {
      prev=temp;
      temp=temp->next;   
    }
    if (prev) {
      new->next = temp;
      new->prev = prev;
      prev->next = new;
      if (temp) // if not at end
	temp->prev = new;
      else
	list->tail = new;
    } else {
      list->head->prev = new;
      new->next = list->head;
      list->head = new;
    }
  }  
  list->size++;
  return new;
}

// AssembleVector: Helper function for generating vector code.
//               It figures out how to assemble a vector from two inputs under
//               the assumption that the inputs are either constants or registers.
//               If constants, it builds a constant vector.  If registers,
//               it emits the insertelement instructions.
//  
//               This is only helpful for generating vector code, not for detecting
//               vectorization opportunities

static LLVMValueRef AssembleVector(LLVMValueRef a, LLVMValueRef b)
{
  LLVMTypeRef type = LLVMTypeOf(a);
  LLVMValueRef ret;

  // if they are constants...
  if (LLVMIsAConstant(a) && LLVMIsAConstant(b)) {
    // Build constant vector
    LLVMValueRef vec[2] = {a,b};
    ret = LLVMConstVector(vec,2);        
  }  else {
    // Otherwise, one of them is a register

    LLVMTypeRef vtype = LLVMVectorType(type,2);
    LLVMValueRef c = LLVMConstNull(vtype);
    
    // Insert a into null vector
    ret = LLVMBuildInsertElement(Builder,c,a,
				 LLVMConstInt(LLVMInt32Type(),0,0),"v.ie");

    // Insert b into ret
    ret = LLVMBuildInsertElement(Builder,ret,b,
				 LLVMConstInt(LLVMInt32Type(),1,0),"v.ie");    
  }

  // Return new vector as input for a new vector instruction
  return ret;
}


static LLVMValueRef myBuild(LLVMValueRef I,LLVMValueRef* ops){
 LLVMValueRef ret;
 LLVMTypeRef type;
 LLVMTypeRef vtype;
 switch(LLVMGetInstructionOpcode(I)){
  case LLVMAdd:
   ret=LLVMBuildAdd(Builder,ops[0],ops[1],"");
   break; 
  case LLVMFAdd:
   ret=LLVMBuildFAdd(Builder,ops[0],ops[1],"");
   break;
  case LLVMSub:
   ret=LLVMBuildSub(Builder,ops[0],ops[1],"");
   break;
  case LLVMFSub:
   ret=LLVMBuildFSub(Builder,ops[0],ops[1],"");
   break; 
  case LLVMMul:
   ret=LLVMBuildMul(Builder,ops[0],ops[1],"");
   break;
  case LLVMFMul:
   ret=LLVMBuildFMul(Builder,ops[0],ops[1],"");
   break;
  case LLVMUDiv:
   ret=LLVMBuildUDiv(Builder,ops[0],ops[1],"");
   break;
  case LLVMSDiv:
   ret=LLVMBuildSDiv(Builder,ops[0],ops[1],"");
   break;
  case LLVMFDiv:
   ret=LLVMBuildFDiv(Builder,ops[0],ops[1],"");
   break;
  case LLVMURem:
   ret=LLVMBuildURem(Builder,ops[0],ops[1],"");
   break;
  case LLVMSRem:
   ret=LLVMBuildSRem(Builder,ops[0],ops[1],"");
   break;
  case LLVMFRem:
   ret=LLVMBuildFRem(Builder,ops[0],ops[1],"");
   break;
  case LLVMShl:
   ret=LLVMBuildShl(Builder,ops[0],ops[1],"");
   break;
  case LLVMLShr:
   ret=LLVMBuildLShr(Builder,ops[0],ops[1],"");
   break;
  case LLVMAShr:
   ret=LLVMBuildAShr(Builder,ops[0],ops[1],"");
   break;
  case LLVMAnd:
   ret=LLVMBuildAnd(Builder,ops[0],ops[1],"");
   break;
  case LLVMOr:
   ret=LLVMBuildOr(Builder,ops[0],ops[1],"");
   break;
  case LLVMXor:
   ret=LLVMBuildXor(Builder,ops[0],ops[1],"");
   break;
  case LLVMAlloca:
   ret=LLVMBuildAlloca(Builder,LLVMVectorType(LLVMGetElementType(LLVMTypeOf(I)),2),"");
   break;
  case LLVMLoad:
   ret=LLVMBuildLoad(Builder,ops[0],"");
   break;
  case LLVMStore:
   ret=LLVMBuildStore(Builder,ops[0],ops[1]);
   break;
  case LLVMGetElementPtr:
   ret = LLVMBuildGEP(Builder,ops[0],&ops[1],LLVMGetNumOperands(I)-1,"v.gep");
  case LLVMTrunc:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildTrunc(Builder,ops[0],vtype,"");
   //ret=LLVMBuildTrunc(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMZExt:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildZExt(Builder,ops[0],vtype,"");
   //ret=LLVMBuildZExt(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMSExt: 
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildSExt(Builder,ops[0],vtype,"");
//   ret=LLVMBuildSExt(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMFPToUI:  
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildFPToUI(Builder,ops[0],vtype,"");
//   ret=LLVMBuildFPToUI(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMFPToSI:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildFPToSI(Builder,ops[0],vtype,"");
//   ret=LLVMBuildFPToSI(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMUIToFP:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildUIToFP(Builder,ops[0],vtype,"");
//   ret=LLVMBuildUIToFP(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMSIToFP:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildSIToFP(Builder,ops[0],vtype,"");
//   ret=LLVMBuildSIToFP(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMFPTrunc:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildFPTrunc(Builder,ops[0],vtype,"");
//   ret=LLVMBuildFPTrunc(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMFPExt:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildFPExt(Builder,ops[0],vtype,"");
   break;
  case LLVMPtrToInt:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildPtrToInt(Builder,ops[0],vtype,"");
  // ret=LLVMBuildPtrToInt(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMIntToPtr:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildIntToPtr(Builder,ops[0],vtype,"");
//   ret=LLVMBuildIntToPtr(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  case LLVMBitCast:
   type=LLVMTypeOf(I);  //
   vtype = LLVMVectorType(type,2);
   ret = LLVMBuildBitCast(Builder,ops[0],vtype,"");
//   ret=LLVMBuildBitCast(Builder,ops[0],LLVMTypeOf(I),"");
   break;
  default:
   return NULL;
 }
 return ret;
}

/*void vectorize(VectorList* L){
	LLVMValueRef *ops;
	LLVMBasicBlockRef bb;
	valmap_t vmap = valmap_create();
	VectorPair *temp = L->head;	
	LLVMValueRef I,J,K;
	int check;
	while(temp != NULL){
		I = temp->pair[0];
		J = temp->pair[1];
		check = dom(I,J);
		if(!check){
			K = I;
			I = J;
			J = K;	
		}
		ops = (LLVMValueRef *)malloc(sizeof(VectorList)*LLVMGetNumOperands(I));
		int i;
		for(i=0;i<LLVMGetNumOperands(I);i++){
			if(valmap_check(vmap,LLVMGetOperand(I,i))){
				ops[i] = valmap_find(vmap,LLVMGetOperand(I,i));	
			}
			else{
				ops[i] = AssembleVector(LLVMGetOperand(I,i),LLVMGetOperand(J,i));
				valmap_insert(vmap,LLVMGetOperand(I,i),ops[i]);
				valmap_insert(vmap,LLVMGetOperand(J,i),ops[i]);
			}
		}
		if(!check){
			LLVMPositionBuilderBefore(Builder,I);
		}
		else{
			LLVMPositionBuilderBefore(Builder,J);
		}
	}

}*/

void vectorize(VectorList* list){
LLVMValueRef* ops;
  LLVMBasicBlockRef bb;
  valmap_t vmap = valmap_create();
  valmap_t vnew = valmap_create();
  int i,useI,useJ;
  VectorPair* head=list->head;
  while(head!=NULL){
    LLVMValueRef J=head->pair[0];                                              
    LLVMValueRef I=head->pair[1];
    bb=LLVMGetInstructionParent(I);
    ops = (LLVMValueRef*) malloc(sizeof(VectorList)*LLVMGetNumOperands(I));
    for(i=0;i<LLVMGetNumOperands(I);i++){
      if(!valmap_check(vmap,LLVMGetOperand(I,i))){
        ops[i]=AssembleVector(LLVMGetOperand(I,i),LLVMGetOperand(J,i));
        valmap_insert(vmap,LLVMGetOperand(I,i),ops[i]);
        valmap_insert(vmap,LLVMGetOperand(J,i),ops[i]);
      }
      else
       ops[i]=valmap_find(vmap,LLVMGetOperand(I,i));
    }
   // LLVMPositionBuilderBefore(Builder,J);
  }
    /*LLVMValueRef newIns;
    newIns = myBuild(I,ops);
    valmap_insert(vmap,I,newIns);
    valmap_insert(vmap,J,newIns);
    LLVMUseRef it;
    LLVMValueRef index;
    for(it=LLVMGetFirstUse(I);it!=NULL;it=LLVMGetNextUse(it)){
      LLVMValueRef temp=LLVMGetUser(it);
      if(!valmap_check(list->visited,temp)){
        useI=1;
        break;
      }
    } 
    for(it=LLVMGetFirstUse(J);it!=NULL;it=LLVMGetNextUse(it)){
      LLVMValueRef temp=LLVMGetUser(it);
      if(!valmap_check(list->visited,temp)){
        useJ=1;
        break;
      }
    }
     index=LLVMConstInt(LLVMInt32Type(),0,0);
     LLVMValueRef evi;
     if(LLVMIsAAllocaInst(I)){
       LLVMValueRef indices[2]={LLVMConstInt(LLVMInt32Type(),0,0),LLVMConstInt(LLVMInt32Type(),0,0) };
       evi=LLVMBuildGEP(Builder,valmap_find(vmap,I),indices,2,""); 
     }
     else
       evi=LLVMBuildExtractElement(Builder,valmap_find(vmap,I),index,"");
     
     valmap_insert(vmap,valmap_find(vmap,I),evi);
     valmap_insert(vnew, evi, NULL);
     LLVMReplaceAllUsesWith(I,evi);
   LLVMInstructionEraseFromParent(I);
   
     index=LLVMConstInt(LLVMInt32Type(),0,1);
     LLVMValueRef evj;
     if(LLVMIsAAllocaInst(J)){
       LLVMValueRef indices[2]={LLVMConstInt(LLVMInt32Type(),0,0),LLVMConstInt(LLVMInt32Type(),1,0) };
       evj=LLVMBuildGEP(Builder,valmap_find(vmap,J),indices,2,"");
     }
     else
       evj=LLVMBuildExtractElement(Builder,valmap_find(vmap,J),index,"");
     valmap_insert(vmap,valmap_find(vmap,J),evj);
     valmap_insert(vnew, evj, NULL);
     LLVMReplaceAllUsesWith(J,evj);
   LLVMInstructionEraseFromParent(J);

   head=head->next;
  }
  LLVMValueRef k=LLVMGetFirstInstruction(bb);
  while(k!=NULL){
    if(LLVMGetInstructionOpcode(k) == LLVMExtractElement || LLVMGetInstructionOpcode(k) == LLVMGetElementPtr){
      if(valmap_check(vnew,k)){
        if(LLVMGetFirstUse(k)==NULL){
          LLVMValueRef del=k;
	  k = LLVMGetNextInstruction(k);
          LLVMInstructionEraseFromParent(del);
	  continue;
        }
      }
    }
  k=LLVMGetNextInstruction(k);
  }*/

}



bool AdjacentStores(LLVMValueRef I, LLVMValueRef J)
{
  LLVMValueRef gep1 = LLVMGetOperand(I, 1); 
  LLVMValueRef gep2 = LLVMGetOperand(J, 1);

  if (!LLVMIsAGetElementPtrInst(gep1) || !LLVMIsAGetElementPtrInst(gep2))
    return false;

  if (LLVMGetOperand(gep1, 0) != LLVMGetOperand(gep2, 0))
    return false;

  int num1 = LLVMGetNumOperands(gep1);
  int num2 = LLVMGetNumOperands(gep2);


  for (int i=0; i<(num1-1); i++)
  {
    if (LLVMGetOperand(gep1, i) != LLVMGetOperand(gep2, i)) 
      return false;
  }

  if (!LLVMIsAConstant(LLVMGetOperand(gep1, num1-1)) || !LLVMIsAConstant(LLVMGetOperand(gep2, num2-1)))
    return false;

  int a = LLVMConstIntGetZExtValue(LLVMGetOperand(gep1, num1-1));
  int b = LLVMConstIntGetZExtValue(LLVMGetOperand(gep2, num2-1));
  int c = a-b; 
  if(c < 0){
    if(c != -1)	return false;
  }
  else{
    if(c != 1)	return false;
  }

  return true;
}

bool AdjacentLoads(LLVMValueRef I, LLVMValueRef J)
{
  LLVMValueRef gep1 = LLVMGetOperand(I, 0); 
  LLVMValueRef gep2 = LLVMGetOperand(J, 0);

  if (!LLVMIsAGetElementPtrInst(gep1) || !LLVMIsAGetElementPtrInst(gep2))
    return false;

  if (LLVMGetOperand(gep1, 0) != LLVMGetOperand(gep2, 0))
    return false;

  int num1 = LLVMGetNumOperands(gep1);
  int num2 = LLVMGetNumOperands(gep2);
   

  for (int i=0; i<(num1-1); i++)
  {
    if (LLVMGetOperand(gep1, i) != LLVMGetOperand(gep2, i)) 
      return false;
  }

  if (!LLVMIsAConstant(LLVMGetOperand(gep1, num1-1)) || !LLVMIsAConstant(LLVMGetOperand(gep2, num2-1)))
    return false;

  int a = LLVMConstIntGetZExtValue(LLVMGetOperand(gep1, num1-1));
  int b = LLVMConstIntGetZExtValue(LLVMGetOperand(gep2, num2-1));
  int c = a-b; 
  if(c < 0){
    if(c != -1)	return false;
  }
  else{
    if(c != 1)	return false;
  }

  return true;
}

bool Isomorphic(LLVMValueRef I, LLVMValueRef J)
{
  
  if(!LLVMIsAInstruction(I) || !LLVMIsAInstruction(J))
    return false; 
  if(LLVMGetInstructionOpcode(I) != LLVMGetInstructionOpcode(J))
    return false;
  if(LLVMTypeOf(I) != LLVMTypeOf(J))
    return false;
  if(LLVMGetNumOperands(I) != LLVMGetNumOperands(J))
    return false;
  int i;
  int num = LLVMGetNumOperands(I);
  for(i=0;i<num;i++)
    {
	    if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i))) {
     		 if(LLVMGetInstructionParent(LLVMGetOperand(I,i)) == LLVMGetInstructionParent(LLVMGetOperand(J,i))) {
      			if(LLVMTypeOf(LLVMGetOperand(I,i)) != LLVMTypeOf(LLVMGetOperand(J,i)))
				return false;
		}
	    }
    }

  return true;
}



static int shouldVectorize(LLVMValueRef I, LLVMValueRef J){


	if(LLVMIsALoadInst(I) && LLVMIsALoadInst(J)){
	
		if((LLVMGetTypeKind(LLVMTypeOf(I)) != LLVMIntegerTypeKind) && (LLVMGetTypeKind(LLVMTypeOf(I)) != LLVMFloatTypeKind) && (LLVMGetTypeKind(LLVMTypeOf(I)) == LLVMPointerTypeKind) )	return 0;
	}
	else{
		if((LLVMGetTypeKind(LLVMTypeOf(I)) != LLVMIntegerTypeKind) && (LLVMGetTypeKind(LLVMTypeOf(I)) != LLVMFloatTypeKind) && (LLVMGetTypeKind(LLVMTypeOf(I)) == LLVMPointerTypeKind) && (LLVMGetTypeKind(LLVMTypeOf(I)) != LLVMVoidTypeKind))	return 0;
	}
		
	if(LLVMGetInstructionParent(I) != LLVMGetInstructionParent(J)){
		return 0;
	}

	if(LLVMIsATerminatorInst(I)){
		return 0;
	}	
	if((LLVMIsALoadInst(I) || LLVMIsAStoreInst(I)) && LLVMGetVolatile(I)){
		return 0;
	}	
	
	if(LLVMIsAPHINode(I) || LLVMIsACallInst(I) || LLVMIsAFCmpInst(I) || LLVMIsAICmpInst(I) ||  LLVMIsAAddrSpaceCastInst(I) || LLVMIsAExtractValueInst(I) || LLVMIsAExtractElementInst(I) || LLVMIsAInsertValueInst(I) || (LLVMGetInstructionOpcode(I) == LLVMAtomicCmpXchg)  || (LLVMGetInstructionOpcode(I) == LLVMAtomicRMW) ||  (LLVMGetInstructionOpcode(I) == LLVMFence) || (LLVMGetInstructionOpcode(I) == LLVMExtractValue)){
		return 0;
	}

	if(LLVMIsAGetElementPtrInst(I) || LLVMIsAGetElementPtrInst(J))	return 0;

	if(LLVMIsALoadInst(I) && LLVMIsALoadInst(J)){
		if(!AdjacentLoads(I,J)){
			return 0;
		}
	}
	if(LLVMIsAStoreInst(I) && LLVMIsAStoreInst(J)){
		if(!AdjacentStores(I,J)){
			return 0;
		}
	}
	

	return 1;
}

static void collectIsomorphicInstruction(VectorList *L,LLVMValueRef I,LLVMValueRef J){
	if(shouldVectorize(I,J) == 0){
		return;
	}
	if(valmap_check(L->visited,I) || valmap_check(L->visited,J)){
		return;
	}
	//printf("13\n");
	VectorList_AppendPair(L,I,J);
	int num = LLVMGetNumOperands(I);
	for(int i=0;i<num;i++){
		//if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i))){
			if(Isomorphic(LLVMGetOperand(I,i),LLVMGetOperand(J,i))){
		//		      if(LLVMIsConstant(LLVMGetOperand(I,i)) && LLVMIsConstant(LLVMGetOperand(J,i))) {
		//			continue;
		//		      }
				collectIsomorphicInstruction(L,LLVMGetOperand(I,i),LLVMGetOperand(J,i));
			}
		//}
	}

}

bool NotVector(VectorList *List,LLVMValueRef I){

	VectorPair *traverse = List->head;
	while(traverse != NULL){
		if(traverse -> pair[0] == I || traverse -> pair[1] == I)	return false;
		traverse = traverse->next;
	}	
	return true;
}






static void SLPOnBasicBlock(LLVMBasicBlockRef BB)
{
  LLVMValueRef I;
  int changed;
  int i=0;
  VectorList *LIST;
  LIST = VectorList_Create();
  for(I=LLVMGetLastInstruction(BB);
      I!=NULL;
      I=LLVMGetPreviousInstruction(I))
    {
	//printf("1\n");
	VectorList *L;
	L =  VectorList_Create();
	//if(!valmap_check(LIST->visited,I)){
	//	VectorList_AppendPair(LIST,I,I);		
		if(LLVMIsAStoreInst(I) && NotVector(LIST,I)){
			//printf("2\n");
		
			LLVMValueRef J = LLVMGetPreviousInstruction(I);
			while(J != NULL){
				if(LLVMIsAStoreInst(J)){
					if(AdjacentStores(I,J)){
						if(Isomorphic(I,J)){
							if(NotVector(LIST,J)){
								printf("7\n");
								collectIsomorphicInstruction(L,I,J);
								if(L->size >= 2){
									break;
								} 
							}
						}
					}
				}
				//printf("8\n");
				J = LLVMGetPreviousInstruction(J);
			}
			int k;
			if(L->head != NULL){
				VectorPair *temp = L->head;
				while(temp!=NULL){
					VectorList_AppendPair(LIST,temp->pair[0],temp->pair[1]);
					temp = temp->next;
				}
			}
			

				if(L->size == 1)	array[6]++;

				if(L->size == 2){
					array[0]++;
				}
				if(L->size == 3){
					array[1]++;
				}
				if(L->size == 4){
					array[2]++;
				}
				if(L->size >= 5){
					array[3]++;
				}
				if(L->size > 0){
					array[4]++;
					vectorize(L);
				}
		}
	//}
	if(LLVMIsALoadInst(I) && NotVector(LIST,I)){
		LLVMValueRef J = LLVMGetNextInstruction(I);
		while(J != NULL){
			if(LLVMIsALoadInst(J)){
				if(AdjacentLoads(I,J)){
					if(Isomorphic(I,J)){
						if(NotVector(LIST,J)){
						//printf("7\n");
							collectIsomorphicInstruction(L,I,J);
							if(L->size >= 2){
								break;
							} 
						}
					}
				}
			}
			//printf("8\n");
			J = LLVMGetNextInstruction(J);
		}
		int k;
		if(L->head != NULL){
			VectorPair *temp = L->head;
			while(temp!=NULL){
				VectorList_AppendPair(LIST,temp->pair[0],temp->pair[1]);
				temp = temp->next;
			}
		}
		

			
			if(L->size == 1)	array[6]++;		
			
			if(L->size == 2){
				array[0]++;
			}
			if(L->size == 3){
				array[1]++;
			}
			if(L->size == 4){
				array[2]++;
			}
			if(L->size >= 5){
				array[3]++;
			}
			if(L->size > 0){
				array[5]++;
				vectorize(L);
			}
    }
   }
}

static void SLPOnFunction(LLVMValueRef F) 
{
  LLVMBasicBlockRef BB;
  for(BB=LLVMGetFirstBasicBlock(F);
      BB!=NULL;
      BB=LLVMGetNextBasicBlock(BB))
    {
      SLPOnBasicBlock(BB);
    }
}

void SLP_C(LLVMModuleRef Module)
{
  LLVMValueRef F;
  for(F=LLVMGetFirstFunction(Module); 
      F!=NULL;
      F=LLVMGetNextFunction(F))
    {
      SLPOnFunction(F);
    }
  printf("SLP Results:\n");
  printf("Size: Count\n");
  printf(" 1: %d\n",array[6]);
  printf(" 2: %d\n",array[0]);
  printf(" 3: %d\n",array[1]);
  printf(" 4: %d\n",array[2]);
  printf(">5: %d\n",array[3]);
  printf("Store-chain: %d\n",array[4]);
  printf("Load-chain: %d\n",array[5]);
}

