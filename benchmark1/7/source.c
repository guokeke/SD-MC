//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: [](AP(added>=0) ==> <>[]AP(ret==1));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
#include <stdio.h>
#define 1 1
#define 2 2
#define 3 3
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()

#define HAVE_IPV6 1
#define HAVE_UNIX_SOCKETS 1
#define PG_SOMAXCONN 10
#define SOCK_STREAM 1
#define STATUS_ERROR 0
#define STATUS_OK 1
#define gettext(a) ""
#define ereport(a,b,c) __VERIFIER_nondet_int()
#define getaddrinfo_all(a,b,c,d) __VERIFIER_nondet_int()
#define listen(a,b) __VERIFIER_nondet_int()
#define snprintf(a,b,c,f) {}
#define errmsg(a,b,c,d) ()
#define errcode_for_socket_access() 1
#define LOG 0
#define closesocket(a) { closed=1; }
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
#define __builtin___object_size(a,b) __VERIFIER_nondet_int()
#define socket(a,b,c) { return __VERIFIER_nondet_int(); }

int closed;
int MaxBackends;
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



void main()
{
	one = 1;
	listen_index = 0;
	added = 0;
	MAXADDR = rand();
	addrs = rand();
	MaxBackends = rand();
	ret = rand();
	//__VERIFIER_assume(addrs >= 0);
	//__VERIFIER_assume(MaxBackends>0);

	if (family == 3)
	{
		service = sock_path;
	}
	else
	{
		snprintf(1, sizeof(1), "%d", portNumber);
		service = (char*)1;
	}

	/*ret = rand();
	if (ret || !addrs)
	{
		if (hostName)
		{

		}
		else
		{

		}
	}*/
	addr = addrs;
	while (addr < MAXADDR)
	{
		int rand_x = rand();
		int rand_x1 = rand();
		if (!rand_x)
		{
			if (rand_x1)
			{
				goto loc_continue;
			}
		}

		while(listen_index < MaxListen)
		{
			if (ListenSocket_OF_listen_index == -1)
				break;
			listen_index++;
		}
		if (listen_index >= MaxListen)
		{
			break;
		}

		if (addr_ai_family == 1)
		{
			//gettext("IPv4");
		}
		else if (addr_ai_family == 2)
		{
			//gettext("IPv6");
		}
		else if (addr_ai_family == 3)
		{
			//gettext("Unix");
		}
		else
		{
			snprintf(1, 1, "", addr_ai_family);
		}

		fd = rand();
		if (fd)
		{
			goto loc_continue;
		}

		int rand_x2 = rand();
		if (rand_x2)
		{
			int rand_x3 = rand();
			if (rand_x3)
			{
				goto loc_continue;
			}
		}

		int rand_x4 = rand();
		if (rand_x4)
		{
			int rand_x5 = rand();
			if (rand_x5)
			{
				closesocket(fd);
				goto loc_continue;
			}
		}

		err = rand();
		if (err < 0)
		{
			closesocket(fd);
			goto loc_continue;
		}

		if (addr_ai_family == 3)
		{
			int rand_x6 = rand();
			if (rand_x6 != STATUS_OK)
			{
				closesocket(fd);
				break;
			}
		}

		maxconn = MaxBackends * 2;
		if (maxconn > PG_SOMAXCONN)
			maxconn = PG_SOMAXCONN;

		err = rand();
		if (err < 0)
		{
			closesocket(fd);
			goto loc_continue;
		}

		ListenSocket_OF_listen_index = fd;
		added++;

		if (1)
		{
		loc_continue: 0;
		}

		addr++;
	}

	if (!added)
	{
		ret = STATUS_ERROR;
		//while (1) { int rrr = 0; rrr = rrr; }
	}

	ret = STATUS_ERROR;
	//while (1) { int ddd = 0; ddd = ddd; }
}
