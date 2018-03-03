//#Unsafe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: AP(c > 5) ==> <>AP(resp > 5);

//extern void __VERIFIER_error() __attribute__ ((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include<stdlib.h>

int c;
int servers ;
int resp;
int curr_serv;


int main() {
	c = rand();
	servers = 4;
	resp = 0;
	curr_serv = servers;
//__VERIFIER_assume(c>0);
  while(curr_serv > 0) {
	  int rand_x = rand();
	  if (rand_x) {
         c--; curr_serv--;
         resp++;
      } else {
      //__VERIFIER_assume(c < curr_serv);
      curr_serv--;
      }
  }
  while(1) { int ddd; ddd=ddd; }
}

