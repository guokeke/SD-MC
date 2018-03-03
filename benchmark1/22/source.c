//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: <>[]AP(WItemsNum >= 1 );

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
int WItemsNum;

void callback1() {}
void callback2() {}
//#define MoreWItems() __VERIFIER_nondet_int()

void main() {
	WItemsNum = rand();
	
	//while (1) {
		int rand_x = rand();
		while (1) {
			if (!(WItemsNum<=5)){
			   if (!rand_x){
				   break;
			   }
			}

		    if (WItemsNum<=5) {
				callback1();
				WItemsNum++;

			}
			else {
				WItemsNum++;
			}
			rand_x = rand();
		}

		while (WItemsNum>2) {
			callback2();
			WItemsNum--;
		}
	//}
	//while (1) {}
}
