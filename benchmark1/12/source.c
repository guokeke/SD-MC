//#Safe
//
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: []((<>AP(lr>0) || <>AP(status!=7)) || AP(do_ACCEPT!=1));

//extern void __VERIFIER_error() __attribute__((__noreturn__));
//extern void __VERIFIER_assume();
//extern int __VERIFIER_nondet_int();
#include <stdlib.h>
int do_ACCEPT;

int accept_mutex_off() { int rand_x=rand(); return rand_x; }
int unixd_setup_child() { int rand_x = rand(); return rand_x; }
int APR_STATUS_IS_EINTR(int a) { int rand_x = rand(); return rand_x; }
int accept_mutex_on() { int rand_x = rand(); return rand_x; }
int SAFE_ACCEPT(int a) { int rand_x = rand(); return rand_x; }
int clean_child_exit(int a) { int rand_x = rand(); return rand_x; }

int  ap_accept_lock_mech;
int  ap_listeners;
int  ap_lock_fname;
int  ap_max_mem_free;
int  ap_max_requests_per_child;
int  ap_scoreboard_image;
int  conn_rec;
int  current_conn;
int  numdesc;
int  pfd;
int  shutdown_pending;
int        pfd_desc_type;
int        pfd_desc_s;
int        pfd_reqevents;
int        pfd_client_data;
int temp1;
int temp2;
int temp3;
int temp4;

static volatile int die_now;
static int requests_this_child;
static int num_listensocks = 0;

void *ptrans;
void *allocator;
int status;
int i;
int lr;
void *pollset;
void *sbh;
void *bucket_alloc;
int last_poll_idx;
int child_num_arg;
int ap_threads_per_child;         /* Worker threads per child */
static void *accept_mutex;
static int ap_daemons_to_start = 0;
static int ap_daemons_min_free = 0;
static int ap_daemons_max_free = 0;
static int ap_daemons_limit = 0;      /* MaxClients */
static int server_limit = 256;
static int first_server_limit = 0;
static int changed_limit_at_restart;
static int mpm_state = 1;//9;
static void *pod;
int ap_max_daemons_limit = -1;
void *ap_server_conf;
static int one_process = 0;
static void *pconf;               /* Pool for config stuff */
static void *pchild;              /* Pool for httpd child stuff */

static int ap_my_pid; /* it seems silly to call getpid all the time */
static int parent_pid;
static int my_child_num;
int ap_my_generation = 0;
int tpf_child = 0;
char *tpf_server_name; // [256+1]; // INETD_SERVNAME_LENGTH+1];


/*****************************************************************
* Child process main loop.
* The following vars are static to avoid getting clobbered by longjmp();
* they are really private to child_main.
*/
int getpid() { int rand_x = rand(); return rand_x; }
void ap_fatal_signal_child_setup(int ap_server_conf) {}
void apr_allocator_create(int *allocator) {}
void apr_allocator_max_free_set(int allocator, int ap_max_mem_free) {}
void apr_pool_create_ex(int *pchild, int pconf, int NL, int allocator) {}
void apr_allocator_owner_set(int allocator, int pchild) {}
void apr_pool_create(int *ptrans, int pchild) {}
void apr_pool_tag(int ptrans, char *asdf) {}
void ap_reopen_scoreboard(int pchild, int NL, int z) {}
int apr_proc_mutex_child_init(int *accept_mutex, int ap_lock_fname, int pchild) { int rand_x = rand(); return rand_x; }
void ap_log_error(int APm, int APe, int status, int ap_server_conf, int a, int b, int c) {}
void ap_log_error5(int APm, int APe, int status, int ap_server_conf, int a) {}
void ap_run_child_init(int pchild, int ap_server_conf) {}
void ap_create_sb_handle(int *sbh, int pchild, int my_child_num, int z) {}
void ap_update_child_status(int sbh, int SER, int NL) {}
void apr_pollset_create(int *pollset, int num_listensocks, int pchild, int z) {}
void apr_pollset_add(int pollset, int *pfd) {}
void *apr_bucket_alloc_create(int pchild) { int rand_x = rand(); return (void*)rand_x; }
void apr_pool_clear(int ptrans) {}
int apr_pollset_poll(int pollset, int a, int *numdesc, int *pdesc) { int rand_x = rand(); return rand_x; }
int ap_run_create_connection(int ptrans, int ap_server_conf, int csd, int my_child_num, int sbh, int bucket_alloc) { int rand_x = rand(); return rand_x; }
void ap_process_connection(int current_conn, int csd) {}
void ap_lingering_close(int current_conn) {}
int ap_mpm_pod_check(int a) { int rand_x = rand(); return rand_x; }

//static void child_main(int child_num_arg)
void main()
{
	child_num_arg = rand();

	do_ACCEPT = 0;
	die_now = 0;
	last_poll_idx = 0;
	ap_threads_per_child = 0;
	ap_daemons_to_start = 0;
	ap_daemons_min_free = 0;
	ap_daemons_max_free = 0;
	ap_daemons_limit = 0;      /* MaxClients */
	server_limit = 256;
	first_server_limit = 0;
	ap_listeners = rand();
	
	//__VERIFIER_assume(child_num_arg > 0);
	//__VERIFIER_assume(ap_listeners > 0);



	mpm_state = 9; /* for benefit of any hooks that run as this
								  * child initializes
								  */

	my_child_num = child_num_arg;
	ap_my_pid = getpid();
	requests_this_child = 0;

	ap_fatal_signal_child_setup((int)ap_server_conf);

	/* Get a sub context for global allocations in this child, so that
	* we can have cleanups occur when the child exits.
	*/
	apr_allocator_create((int*)&allocator);
	apr_allocator_max_free_set((int)allocator, ap_max_mem_free);
	apr_pool_create_ex((int*)&pchild, (int)pconf, 0, (int)allocator);
	apr_allocator_owner_set((int)allocator, (int)pchild);

	apr_pool_create((int*)&ptrans, (int)pchild);
	apr_pool_tag((int)ptrans, "transaction");

	/* needs to be done before we switch UIDs so we have permissions */
	ap_reopen_scoreboard((int)pchild, 0, 0);
	status = apr_proc_mutex_child_init((int*)&accept_mutex, ap_lock_fname, (int)pchild);
	if (status!=7) {
		ap_log_error(3, 1, status, (int)ap_server_conf,
			(int)"Couldn't initialize cross-process lock in child "
			"(%s) (%d)", ap_lock_fname, ap_accept_lock_mech);
		clean_child_exit(1);
	}

	temp1 = unixd_setup_child();
	if (temp1!=0) {
		clean_child_exit(1);
	}

	ap_run_child_init((int)pchild, (int)ap_server_conf);

	ap_create_sb_handle((int*)&sbh, (int)pchild, my_child_num, 0);

	ap_update_child_status((int)sbh, 1, 0);

	/* Set up the pollfd array */
	/* ### check the status */
	(void)apr_pollset_create((int*)&pollset, num_listensocks, (int)pchild, 0);

	num_listensocks = rand(); 
	//__VERIFIER_assume(num_listensocks>0);

	lr = ap_listeners;
	i = num_listensocks;
	while(i!=0) {
		i = i - 1;
		int pfd = 0;

		pfd_desc_type = 6;
		pfd_desc_s = 1; // lr->sd;
		pfd_reqevents = 5;
		pfd_client_data = lr;

		/* ### check the status */
		(void)apr_pollset_add((int)pollset, &pfd);
	}
	i = i - 1;

	mpm_state = 8;

	bucket_alloc = apr_bucket_alloc_create((int)pchild);

	while (!die_now) {
		conn_rec *current_conn;


		void *csd=0;

		/*
		* (Re)initialize this child to a pre-connection state.
		*/

		apr_pool_clear((int)ptrans);

		if (ap_max_requests_per_child>0) {
			if (requests_this_child>=ap_max_requests_per_child){
				requests_this_child = requests_this_child + 1;
				clean_child_exit(0);
			}
			requests_this_child = requests_this_child + 1;
		}

		(void)ap_update_child_status((int)sbh, 1, 0);

		/*
		* Wait for an acceptable connection to arrive.
		*/

		/* Lock around "accept", if necessary */
		SAFE_ACCEPT(accept_mutex_on());
		do_ACCEPT = 1; 
		do_ACCEPT = 0;

		if (num_listensocks==1) {
			/* There is only one listener record, so refer to that one. */
			lr = ap_listeners;
		}
		else {
			/* multiple listening sockets - need to poll */
			while(1){
				int numdesc;
				const void *pdesc;

				/* timeout == -1 == wait forever */
				status = apr_pollset_poll((int)pollset, -1, &numdesc, (int*)&pdesc);
				
				if (status!=7) {
					temp2 = APR_STATUS_IS_EINTR(status);
					if (temp2!=0) {
						if (one_process!=0) {
							if (shutdown_pending!=0){
								return;
							}
						}
						continue;
					}
					/* Single Unix documents select as returning errnos
					* EBADF, EINTR, and EINVAL... and in none of those
					* cases does it make sense to continue.  In fact
					* on Linux 2.0.x we seem to end up with EFAULT
					* occasionally, and we'd loop forever due to it.
					*/
					ap_log_error5(3, 2, status,(int)ap_server_conf, (int)"apr_pollset_poll: (listen)");
					clean_child_exit(1);
				}

				/* We can always use pdesc[0], but sockets at position N
				* could end up completely starved of attention in a very
				* busy server. Therefore, we round-robin across the
				* returned set of descriptors. While it is possible that
				* the returned set of descriptors might flip around and
				* continue to starve some sockets, we happen to know the
				* internal pollset implementation retains ordering
				* stability of the sockets. Thus, the round-robin should
				* ensure that a socket will eventually be serviced.
				*/
				if (last_poll_idx>=numdesc)
					last_poll_idx = 0;

				/* Grab a listener record from the client_data of the poll
				* descriptor, and advance our saved index to round-robin
				* the next fetch.
				*
				* ### hmm... this descriptor might have POLLERR rather
				* ### than POLLIN
				*/
				lr = 1; //pdesc[last_poll_idx++].client_data;
				break;

			    //loc_continueA:  {int yyy2=0; yyy2 = yyy2; }
			}
		}
		/* if we accept() something we don't want to die, so we have to
		* defer the exit
		*/
		status = rand(); // lr->accept_func(&csd, lr, ptrans);

		SAFE_ACCEPT(accept_mutex_off());      /* unlock after "accept" */

		if (status==4) {
			/* resource shortage or should-not-occur occured */
			clean_child_exit(1);
		}
		else if (status!=7) {
			continue;
		}

		/*
		* We now have a connection, so set it up with the appropriate
		* socket options, file descriptors, and read/write buffers.
		*/

		current_conn = ap_run_create_connection((int)ptrans, (int)ap_server_conf, (int)csd, my_child_num, (int)sbh, (int)bucket_alloc);
		if (current_conn!=0) {
			ap_process_connection(current_conn, (int)csd);
			ap_lingering_close(current_conn);
		}

		/* Check the pod and the generation number after processing a
		* connection so that we'll go away if a graceful restart occurred
		* while we were processing the connection or we are the lucky
		* idle server process that gets to die.
		*/
		int rand_x = rand();
		temp3 = ap_mpm_pod_check((int)pod);
		if (temp3==7) { /* selected as idle? */
			die_now = 1;
		}
		else if (ap_my_generation!=rand_x) {
			//ap_scoreboard_image->global->running_generation) { /* restart? */
			/* yeah, this could be non-graceful restart, in which case the
			* parent will kill us soon enough, but why bother checking?
			*/
			die_now = 1;
		}
	    //loc_continueB: { int uuu=0; uuu = uuu; }
	}
	clean_child_exit(0);
    loc_return:0;
	//while (1) { int ddd=0; ddd = ddd; }
}
