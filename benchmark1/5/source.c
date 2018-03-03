//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: AP(c > (servers / 2)) ==> <>AP(resp > (servers / 2));
#include<stdlib.h>
//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();

unsigned int c;
int servers;
int s;
int resp;
int curr_serv;
int serversdiv2;

int main() {
	c = rand();
	servers = rand();
	s=servers/2;
	serversdiv2 = rand();
	//__VERIFIER_assume(servers>0 && c > 0); 
	int rand_x = rand();
	if (rand_x)
	{

	}//__VERIFIER_assume(serversdiv2+serversdiv2==servers);
	else
	{

	}
	//__VERIFIER_assume(serversdiv2+serversdiv2+1==servers);
	resp = 0;
	curr_serv = servers;


	while (curr_serv > 0) {
		int rand_x1 = rand();
		if (rand_x1) {
			c--; curr_serv--;
			resp++;
		}
		else {
			//__VERIFIER_assume(c < curr_serv);
			curr_serv--;
		}
	}
	while (1) { int ddd = 0; ddd = ddd; }
}
