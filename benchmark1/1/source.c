//#Safe
// Based on the small program from section 2 of the paper "Cook, Koskinen: Making Prophecies with Decision Predicates"
// manually translated by DD

//@ ltl invariant positive: <>[]AP(x==1);
#include<stdlib.h>
//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();

int x;

void main()
{
	x = 1;

	int rand_x = rand();
	while (rand_x) { rand_x = rand(); }

	x = 0;
	x = 1;
	while (1) {}
}

