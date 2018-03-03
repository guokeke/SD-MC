//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: [](AP(a!= 0) ==> <>AP(r != 0));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
#define NTSTATUS int
#define 2 2
#define 1 1
#define 1 1
#define 3 3
#define int int
#define PLIST_ENTRY int
#define PIRP int
#define KIRQL int
#define ULONG int
#define PIO_STACK_LOCATION int
#define BOOLEAN int
#define TRUE 1
#define FALSE 0

#include<stdio.h>

int a; 
int r;
int irql;
int csl;
int status;
int OldIrql;
int CurrentTimeouts;
int lock;
int k;
int ListElement;
int Irp;
int IrpSp;
int CancelIrql;
int BytesToMove;
int FirstHalf;
int SecondHalf;
int LockHeld;




void KeAcquireSpinLock(int * lp, int * ip) {
	(*lp) = 1;
	(*ip) = irql;
}

void KeReleaseSpinLock(int * lp, int i) {
	(*lp) = 0;
	irql = i;
}


void IoAcquireCancelSpinLock(int * ip) {
	csl = 1;
	(*ip) = irql;
}

void IoReleaseCancelSpinLock(int ip) {
	csl = 0;
	irql = ip;
}

int IoGetCurrentIrpStackLocation(int a) { int rand_x = rand();  return rand_x; }

void RemoveReferenceAndCompleteRequest(int a, int b) {}

void main()
{
	//A = R = 0;
	status = 1;
	CurrentTimeouts = rand();
	k = rand();
	
	a = 1; 
	a = 0; // KeAcquireSpinLock( &lock, &OldIrql);

	
	int rand_x=rand();
	int rand_x1=rand();
	int rand_x2=rand();
	while (1) {
		if (rand_x){
			if (k > 0){
				if (!rand_x1){
					if (!rand_x2){
						break;
					}
				}
			}
			else
			{
				break;
			}
		}
		else
		{
			break;
		}
		
		
        ListElement = rand();
		Irp = rand();
		IrpSp = rand();
		CancelIrql = rand();

		k--;

		Irp = rand();

		IoAcquireCancelSpinLock(&CancelIrql);

		int rand_x3 = rand();
		if (rand_x3) {

			IoReleaseCancelSpinLock(CancelIrql);

			continue;
		}

		// IoSetCancelRoutine(Irp, NULL);
		IoReleaseCancelSpinLock(CancelIrql);
		r = 1; r = 0; // KeReleaseSpinLock(&lock, OldIrql);

		//CALL TO TryToSatisfyRead( deviceExtension);
		{
			status = 1;
			Irp = NULL;
			LockHeld = 1;

			a = 1; a = 0; //KeAcquireSpinLock(&lock,&OldIrql);

			int rand_x4 = rand();
			int rand_x5 = rand();
			if (rand_x4) {
				//
				//  there is an IRP and there are characters waiting
				//
				if (rand_x5){
					Irp = rand();

					IrpSp = IoGetCurrentIrpStackLocation(Irp);

					BytesToMove = rand();

					int rand_x6 = rand();
					if (rand_x6) {
						FirstHalf = rand();

						SecondHalf = BytesToMove - FirstHalf;


					}
					else {
					}
				}
			}
			else
			{
				int rand_x7 = rand();
				if (rand_x7)
				{
					Irp = rand();


					IoAcquireCancelSpinLock(&CancelIrql);

					int rand_x8 = rand();
					if (rand_x8)
					{
						IoReleaseCancelSpinLock(CancelIrql);

						r = 1; r = 0; // KeReleaseSpinLock( &lock, OldIrql);

						RemoveReferenceAndCompleteRequest(Irp,2);
						LockHeld = 0;
					}
					else
					{
						CurrentTimeouts = rand();

						int rand_x8 = rand();
						if (rand_x8)
						{
							IoReleaseCancelSpinLock(CancelIrql);

							r = 1; r = 0; // KeReleaseSpinLock( &lock, OldIrql);

							RemoveReferenceAndCompleteRequest(Irp, 3);

							LockHeld = 0;
						}
						else
						{
							IoReleaseCancelSpinLock(CancelIrql);
							k--;
						}
					}

					Irp = NULL;
				}

			}

			if (LockHeld == 1)
			{
				r = 1; r = 0; //KeReleaseSpinLock( &lock, OldIrql);
			}

			if (Irp != 0) {
				//
				//  if irp isn't null, then we handled one
				//
				RemoveReferenceAndCompleteRequest(Irp, 1);


			}



		}
		//-------------------------------------------------------------
		a = 1; a = 0; // KeAcquireSpinLock(&lock, &OldIrql)
	}

	r = 1; r = 0; //KeReleaseSpinLock( &lock, OldIrql);

	/*while (1) {
		{ int ddd=0; ddd = ddd; }
	}*/
}
