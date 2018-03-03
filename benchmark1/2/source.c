//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: [](AP(set != 0) ==> <> AP(unset!= 0));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
int pc;
int i; int Pdolen; int num; int DName;
int lptNamei; //[5];
int dcIdi; // [5];
int Pdoi; //[5];
int PdoType; int status;

int set = 0;
int unset = 0;

// The Program
int PPMakeDeviceName(int a, int b, int c, int d) { int rand_x = rand(); return rand_x; }
int IoCreateDevice(int a) { int rand_x = rand(); return rand_x; }
void ExFreePool(int a) {}
void PPBlockInits() {}
void PPUnblockInits() {}
void RtlInitUnicodeString(int a) {}


void main() {
	set = 1; set = 0;
	PPBlockInits();
	while (i<Pdolen) {
		DName = PPMakeDeviceName(lptNamei, PdoType, dcIdi, num);
		if (!DName) { break; }
		RtlInitUnicodeString(DName);
		status = IoCreateDevice(Pdoi); pc = 1; pc = 0;
		if (1 != status) {
			Pdoi = 0;
			if (2 == status) {
				ExFreePool(DName);
				num++;
				goto loc_continue;
			}
			break;
		}
		else {
			i++;
		}
	}
	num = 0;
	unset = 1; unset = 0;
	PPUnblockInits();
loc_continue:0;
}
