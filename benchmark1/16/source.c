//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: <>[]AP( Stored == 0 );

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
int Stored;
void init() { Stored = 0; }
void callback() {}
void IoQueueWorkItem() {}
void main() {
	int rand_x = rand();
	while (rand_x!=0) {
		int rand_x1 = rand();
		if (rand_x1!=0) {
			//
			// We are safely at PASSIVE_LEVEL, call callback directly
			// to perform
			// this operation immediately.
			//
			callback();
		}
		else {
			IoQueueWorkItem();
			Stored = 1;
			break;
		}
		rand_x = rand();
	}
	// Lower Irql and process
	if (Stored==1) {
		callback();
		Stored = 0;
	}
}