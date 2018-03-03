//#Unsafe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: AP(istemp==0) ==> [](AP(A!=1));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
#include <stdio.h>
#define AF_INET 1
#define AF_INET6 2
#define AF_UNIX 3
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
//#define __builtin___object_size(a,b) __VERIFIER_nondet_int()
#define BM_DIRTY 1
#define BM_JUST_DIRTIED 2
#define BM_IO_IN_PROGRESS 3

int family;
char *hostName;
unsigned short portNumber;
char *unixSocketName;
int MaxListen;
int fd, err;
int maxconn;
int one;
int ret;
char *service;
int hint;
int listen_index;
int added;
int addr_ai_family;
int addr;
int MAXADDR;
int ListenSocket_OF_listen_index;
char *sock_path;
int addrs;
int rnode;
int istemp;
int firstDelBlock;
int A; 
int RELEASE;
char *bufHdr;
int bufHdr_tag_blockNum;
int bufHdr_tag_rnode;
int bufHdr_tag_rnode_spcNode;
int bufHdr_tag_rnode_dbNode;
int bufHdr_tag_rnode_relNode;
int bufHdr_flags;
int bufHdr_cntxDirty;
int LocalRefCount_i;
int LocalBufferDescriptors_i;
int NLocBuffer;
int i;
int NBuffers;
int bufHdr_refcount;

void StrategyInvalidateBuffer(int bufHdr) {}
void WaitIO(int a) {}
int RelFileNodeEquals(int a, int b)
{
	int rand_x=rand();
	return rand_x;
}



void main() {
	//DD: If NBuffers is not larger than 1, the property is trivially not satisfied. So I added the following line:
	//__VERIFIER_assume(NBuffers>1);
	//end
	istemp = rand();
	A = 0;
	RELEASE = 0;
	NLocBuffer = rand();
	NBuffers = rand();
	if (istemp==1)
	{
		i = 0;
		while(i<NLocBuffer)
		{
			bufHdr = (char*)&LocalBufferDescriptors_i;
			int temp1 = RelFileNodeEquals(bufHdr_tag_rnode, rnode);
			if (temp1)
			{
				if (bufHdr_tag_blockNum>=firstDelBlock){
					
					if (LocalRefCount_i!=0){};

					//DD: replaced the line
					//bufHdr_flags &= ~(BM_DIRTY | BM_JUST_DIRTIED);
					//with this
					bufHdr_flags = 0;
					//because x = 0 & ... is always 0 				
					//end
					bufHdr_cntxDirty = 0;
					bufHdr_tag_rnode_relNode = 1; // InvalidOid;
				}
			}
			i++;
		}
		goto my_exit;
	}

	A = 1; A = 0; // LWLockAcquire(BufMgrLock, LW_EXCLUSIVE);

	i = 1;
	while(i<=NBuffers)
	{
		int rand_x = rand();
		bufHdr = (char*)rand_x; // &BufferDescriptors[i - 1];
	recheck:
		
		int temp2 = RelFileNodeEquals(bufHdr_tag_rnode, rnode);
		if (bufHdr_tag_blockNum>=firstDelBlock)
		{
			if (bufHdr_tag_blockNum>=firstDelBlock)
			{
				//DD: replaced the line
				//if (bufHdr_flags & BM_IO_IN_PROGRESS)
				//with this
				if (bufHdr_flags)
				{
					WaitIO((int)bufHdr);
					goto recheck;
				}

				if (bufHdr_refcount!=0);

				//DD: replaced the line
				//bufHdr_flags &= ~(BM_DIRTY | BM_JUST_DIRTIED);
				//with this
				bufHdr_flags = 0;
				//because x = 0 & ... is always 0 
				//end
				bufHdr_cntxDirty = 0;

				StrategyInvalidateBuffer((int)bufHdr);
			}
		}
		i++;
	}

	RELEASE = 1; RELEASE = 0; //LWLockRelease(BufMgrLock);
my_exit:0;
	//while (1) { i;nt yyy=0; yyy = yyy; }
}
