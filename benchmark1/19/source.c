//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: []( AP(lock == 1) ==> <>AP( lock == 0));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include<stdlib.h>
/*#define NTSTATUS int
#define PIRP int
#define PDEVICE_OBJECT int
#define KIRQL int*/
#include<stdio.h>
/*#define 1 1
#define 2 2
#define 3 3
#define 4 4
#define IOCTL_SERIAL_SET_WAIT_MASK 5
#define ULONG int
#define IOCTL_SERIAL_WAIT_ON_MASK 6
#define 7 7
#define IOCTL_SERIAL_PURGE 8
#define PULONG int
#define IOCTL_SERIAL_GET_MODEMSTATUS 9
#define 10 10
#define 11 11
#define IOCTL_SERIAL_SET_TIMEOUTS 12
#define PSERIAL_TIMEOUTS int
#define PSERIAL_STATUS int
#define PSERIAL_BAUD_RATE int
#define SERIAL_TIMEOUTS 14
#define 15 15
#define IOCTL_SERIAL_GET_TIMEOUTS 16
#define IOCTL_SERIAL_SET_DTR 17
#define IOCTL_SERIAL_CLR_DTR 18
#define IOCTL_SERIAL_GET_COMMSTATUS 19
#define IOCTL_SERIAL_GET_BAUD_RATE 20
#define IOCTL_SERIAL_SET_BAUD_RATE 21
#define IOCTL_SERIAL_SET_QUEUE_SIZE 22
#define SERIAL_BAUD_RATE int
#define IOCTL_SERIAL_SET_LINE_CONTROL 23
#define UCHAR int
#define SERIAL_LINE_CONTROL int
#define PSERIAL_LINE_CONTROL int
#define 24 24
#define 25 25
#define 26 26
#define 27 27
#define 28 28
#define 29 29
#define 30 30
#define 31 31
#define 32 32
#define 33 33
#define 34 34
#define 35 35
#define 36 36
#define 37 37
#define 28 28
#define 29 29
#define 30 30
#define 31 31
#define 32 32
#define 33 33
#define 34 34
#define 35 35
#define 36 36
#define 37 37
#define 38 38
#define 39 39
#define 40 40
#define 41 41*/
int lock;
int CancelIrql;
int irql;
int csl;
int    CurrentWaitIrp = 0;
int NewMask;
int CancelIrp;
int Mask;
int length;
int NewTimeouts;
int SerialStatus;
int pBaudRate;
int pLineControl;
int LData;
int LStop;
int LParity;

int keA;
int keR;
/*
void KeAcquireSpinLock(int * lp, int * ip) {
(*lp) = 1;
(*ip) = irql;
}
*/
/*
void KeReleaseSpinLock(int * lp, int i) {
(*lp) = 0;
irql = i;
}
*/
void IoAcquireCancelSpinLock(int * ip) {
	csl = 1;
	(*ip) = irql;
}
void IoReleaseCancelSpinLock(int ip) {
	csl = 0;
	irql = ip;
}
void IoMarkIrpPending(int x) {}
// This could be modelled in more detail
void RemoveReferenceAndCompleteRequest(int x, int y) {}
// This could be modelled in more detail
void RemoveReferenceForDispatch(int x) {}
// This could be modelled in more detail
void ProcessConnectionStateChange(int x) {}
int DeviceObject;
int Irp;
int          status;
int             OldIrql;

int main()
{
	keA = 0;
	keR = 0;
	//DD: init lock with 0 to avoid trivial satisfaction
	lock = 0;
	CancelIrql = rand();
	irql = rand();
	csl = rand();
	DeviceObject = rand();
	Irp = rand();
	status = 1;
	OldIrql;
	status = rand();
	keA = 0;
	keR = 0;
	length = rand();
	NewTimeouts = rand();
	SerialStatus = rand();
	pBaudRate = rand();
	pLineControl = rand();
	LData = 0;
	LStop = 0;
	LParity = 0;
	Mask = 0xff;
	if (2!=status)
	{
		while (1) { int ddd2=0; ddd2 = ddd2; }
	}

	if (1)
	{
		int rand_x = rand();
		int rand_x2 = rand();
		int rand_x4 = rand();
		int rand_x7 = rand();
		int rand_x11 = rand();
		int rand_x13 = rand();
		int rand_x16 = rand();
		int rand_x18 = rand();
		int rand_x20 = rand();
		int rand_x23 = rand();
		int rand_x25 = rand();
		int rand_x27 = rand();
		int rand_x29 = rand();
		int rand_x30 = rand();
		int rand_x31 = rand();

		if (rand_x!=0)
		{
			int rand_x1 = rand();
			if (rand_x1!=0)
			{
				status = 4;
			}
		}		
		else if (rand_x2!=0)
		{
			CurrentWaitIrp = 0;
			NewMask = rand();

			int rand_x3 = rand();
			if (rand_x3!=0)
			{
				status = 4;
			}
			else
			{
				keA = 1; keA = 0;
				lock = 1; OldIrql = irql;
				NewMask = rand();
				keR = 1; keR = 0;
				lock = 0; irql = OldIrql;
				if (CurrentWaitIrp!=0)
				{
					RemoveReferenceAndCompleteRequest(CurrentWaitIrp, 2);
				}
			}
		}
		else if (rand_x4!=0)
		{
			CurrentWaitIrp = 0;

			int rand_x5 = rand();
			if (rand_x5!=0)
			{
				status = 4;
			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			CurrentWaitIrp = rand();

			int rand_x6 = rand();
			if (rand_x6!=0)
			{
				status = 1;
			}
			else
			{
				IoMarkIrpPending(Irp);
				status = 7;
			}
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
			if (CurrentWaitIrp!=0)
			{
				RemoveReferenceAndCompleteRequest(CurrentWaitIrp, 2);
			}
		}
		else if (rand_x7!=0)
		{
			CancelIrp = rand();
			Mask = rand();

			int rand_x8 = rand();
			if (rand_x8!=0)
			{
				status = 4;
			}
			//DD: Changed & to && to prevent LassoRanker error
			if (Mask!=0)
			{
				keA = 1; keA = 0;
				lock = 1; OldIrql = irql;
				length = rand();
				while (length>0)
				{
					length--;
					CancelIrp = rand();
					IoAcquireCancelSpinLock(&CancelIrql);

					int rand_x9 = rand();
					if (rand_x9!=0)
					{
						IoReleaseCancelSpinLock(CancelIrql);
						continue;
					}
					IoReleaseCancelSpinLock(CancelIrql);
					keR = 1; keR = 0;
					lock = 0; irql = OldIrql;
					RemoveReferenceAndCompleteRequest(CancelIrp, 11);
					keA = 1; keA = 0;
					lock = 1; OldIrql = irql;
				}
				CancelIrp = NULL;

				int rand_x10 = rand();
				if (rand_x10!=0)
				{
					CancelIrp = rand();
				}
				keR = 1; keR = 0;
				lock = 0; irql = OldIrql;
				if (CancelIrp!=NULL)
				{
					RemoveReferenceAndCompleteRequest(CancelIrp, 11);
				}
			}
		}
		else if (rand_x11!=0)
		{
			int rand_x12 = rand();
			if (rand_x12!=0)
			{
				status = 4;
			}
		}
		else if (rand_x13!=0)
		{
			NewTimeouts = rand();
			int rand_x14 = rand();
			if (rand_x14!=0)
			{
				status = 4;
			}

			int rand_x15 = rand();
			if (rand_x15!=0)
			{
				status = 15;
			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
		}
		else if (rand_x16!=0)
		{
			int rand_x17 = rand();
			if (rand_x17!=0)
			{
				status = 4;
			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
		}
		else if (rand_x18!=0)
		{
			SerialStatus = rand();

			int rand_x19 = rand();
			if (rand_x19!=0)
			{
				status = 4;
			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
		}
		else if (rand_x20!=0)
		{
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;

			int rand_x21 = rand();
			if (rand_x21!=0)
			{
			}
			else
			{
				int rand_x22 = rand();
				if (rand_x22!=0)
				{
				}
			}
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
			ProcessConnectionStateChange(DeviceObject);
		}
		else if (rand_x23!=0)
		{
			int rand_x24 = rand();
			if (rand_x24!=0)
			{
				status = 4;
			}
		}
		else if (rand_x25!=0)
		{
			int rand_x26 = rand();
			if (rand_x26!=0)
			{
				status = 4;
			}
			else
			{
				keA = 1; keA = 0;
				lock = 1; OldIrql = irql;
				keR = 1; keR = 0;
				lock = 0; irql = OldIrql;
			}
		}
		else if (rand_x27!=0)
		{
			pBaudRate = rand();

			int rand_x28 = rand();

			if (rand_x28!=0)
			{
				status = 4;
			}
			else
			{
				keA = 1; keA = 0;
				lock = 1; OldIrql = irql;
				keR = 1; keR = 0;
				lock = 0; irql = OldIrql;
			}
		}
		else if (rand_x29!=0)
		{
			pLineControl = rand();
			LData = 0;
			LStop = 0;
			LParity = 0;
			Mask = 0xff;

			int rand_x30 = rand();
			if (rand_x30!=0)
			{
				status = 4;
			}
			if (1)
			{
				int rand_x31 = rand();
				int rand_x32 = rand();
				int rand_x33 = rand();
				int rand_x34 = rand();

				if (rand_x31!=0) /* case 5:*/
				{
					LData = 27;
					Mask = 0x1f;
				}
				else if (rand_x32!=0) /* case 6:*/
				{
					LData = 24;
					Mask = 0x3f;
				}
				else if (rand_x33!=0) /* case 7:*/
				{
					LData = 25;
					Mask = 0x7f;
				}
				else if (rand_x34!=0) /* case 8:*/
				{
					LData = 26;
				}
				else /*default:*/
				{
					status = 15;
				}
			}
			if (status!=2)
			{
				/*break*/;
			}
			if (1)
			{
				int rand_x35 = rand();
				int rand_x36 = rand();
				int rand_x37 = rand();
				int rand_x38 = rand();
				int rand_x39 = rand();
				
				if (rand_x35!=0)
				{
					LParity = 29;
				}
				else if (rand_x36!=0)
				{
					LParity = 31;
				}
				else if (rand_x37!=0)
				{
					LParity = 33;
				}
				else if (rand_x38!=0)
				{
					LParity = 35;
				}
				else if (rand_x39!=0)
				{
					LParity = 37;
				}
				else
				{
					status = 15;
				}
			}
			if (status!=2)
			{

			}
			if (1)
			{
				int rand_x40 = rand();
				int rand_x41 = rand();
				int rand_x42 = rand();
				int rand_x43 = rand();
				
				if (rand_x40!=0)
				{
					LStop = 32;
				}
				else if (rand_x41!=0)
				{
					if (LData!=27)
					{
						status = 15;
					}
					LStop = 37;
				}
				else if (rand_x42!=0)
				{
					if (LData==27)
					{
						status = 15;
					}
					LStop = 33;
				}
				else
				{
					status = 15;
				}
			}
			if (status!=2)
			{

			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
		}
		else if (rand_x30!=0)
		{
			int rand_x32 = rand();
			if (rand_x32!=0)
			{
				status = 4;
			}
			keA = 1; keA = 0;
			lock = 1; OldIrql = irql;
			keR = 1; keR = 0;
			lock = 0; irql = OldIrql;
		}
		else if (rand_x31!=0)
		{
		}
		else
		{
			status = 41;
		}
	}
	if (status!=7)
	{
		if (Irp!=NULL)
		{
			RemoveReferenceAndCompleteRequest(Irp, status);
		}
	}
	RemoveReferenceForDispatch(DeviceObject);
	//while (1) { int rrr=0; rrr = rrr; }
}