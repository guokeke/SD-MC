frame(fp_executionPath,fp_values,do_ACCEPT,ap_accept_lock_mech,ap_listeners,ap_lock_fname,ap_max_mem_free,ap_max_requests_per_child,ap_scoreboard_image,conn_rec,current_conn,numdesc,pfd,shutdown_pending,pfd_desc_type,pfd_desc_s,pfd_reqevents,pfd_client_data,temp1,temp2,temp3,temp4,die_now,requests_this_child,num_listensocks,ptrans,allocator,status,i,lr,pollset,sbh,bucket_alloc,last_poll_idx,child_num_arg,ap_threads_per_child,accept_mutex,ap_daemons_to_start,ap_daemons_min_free,ap_daemons_max_free,ap_daemons_limit,server_limit,first_server_limit,changed_limit_at_restart,mpm_state,pod,ap_max_daemons_limit,ap_server_conf,one_process,pconf,pchild,ap_my_pid,parent_pid,my_child_num,ap_my_generation,tpf_child,tpf_server_name) and (
FILE* fp_executionPath <==fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int do_ACCEPT and skip;
 function accept_mutex_off ( int RValue )
 {
     frame(accept_mutex_off_rand_x,return) and ( 
     int return<==0 and skip;
     int accept_mutex_off_rand_x and skip;
     //accept_mutex_off_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &accept_mutex_off_rand_x) and skip
	 }
	 else{
	    accept_mutex_off_rand_x:=rand(RValue) 
	 };


     return<==1 and RValue:=accept_mutex_off_rand_x;
     skip
     )
     }; 
  function unixd_setup_child ( int RValue )
 {
     frame(unixd_setup_child_rand_x,return) and ( 
     int return<==0 and skip;
     int unixd_setup_child_rand_x and skip;
     //unixd_setup_child_rand_x:=rand(RValue);
	  if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &unixd_setup_child_rand_x) and skip
	 }
	 else{
	    unixd_setup_child_rand_x:=rand(RValue) 
	 };


     return<==1 and RValue:=unixd_setup_child_rand_x;
     skip
     )
     }; 
  function APR_STATUS_IS_EINTR ( int a,int RValue )
 {
     frame(APR_STATUS_IS_EINTR_rand_x,return) and ( 
     int return<==0 and skip;
     int APR_STATUS_IS_EINTR_rand_x and skip;
     //APR_STATUS_IS_EINTR_rand_x:=rand(RValue);
	   if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &APR_STATUS_IS_EINTR_rand_x) and skip
	 }
	 else{
	    APR_STATUS_IS_EINTR_rand_x:=rand(RValue) 
	 };


     return<==1 and RValue:=APR_STATUS_IS_EINTR_rand_x;
     skip
     )
     }; 
  function accept_mutex_on ( int RValue )
 {
     frame(accept_mutex_on_rand_x,return) and ( 
     int return<==0 and skip;
     int accept_mutex_on_rand_x and skip;
     //accept_mutex_on_rand_x:=rand(RValue);
     if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &accept_mutex_on_rand_x) and skip
	 }
	 else{
	    accept_mutex_on_rand_x:=rand(RValue) 
	 };
	 
	 
	 
	 return<==1 and RValue:=accept_mutex_on_rand_x;
     skip
     )
     }; 
  function SAFE_ACCEPT ( int a,int RValue )
 {
     frame(SAFE_ACCEPT_rand_x,return) and ( 
     int return<==0 and skip;
     int SAFE_ACCEPT_rand_x and skip;
     //SAFE_ACCEPT_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &SAFE_ACCEPT_rand_x) and skip
	 }
	 else{
	    SAFE_ACCEPT_rand_x:=rand(RValue) 
	 };
	 


     return<==1 and RValue:=SAFE_ACCEPT_rand_x;
     skip
     )
     }; 
  function clean_child_exit ( int a,int RValue )
 {
     frame(clean_child_exit_rand_x,return) and ( 
     int return<==0 and skip;
     int clean_child_exit_rand_x and skip;
     //clean_child_exit_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &clean_child_exit_rand_x) and skip
	 }
	 else{
	    clean_child_exit_rand_x:=rand(RValue) 
	 };
	 


     return<==1 and RValue:=clean_child_exit_rand_x;
     skip
     )
     }; 
      int ap_accept_lock_mech and skip;
     int ap_listeners and skip;
     int ap_lock_fname and skip;
     int ap_max_mem_free and skip;
     int ap_max_requests_per_child and skip;
     int ap_scoreboard_image and skip;
     int conn_rec and skip;
     int current_conn and skip;
     int numdesc and skip;
     int pfd and skip;
     int shutdown_pending and skip;
     int pfd_desc_type and skip;
     int pfd_desc_s and skip;
     int pfd_reqevents and skip;
     int pfd_client_data and skip;
     int temp1 and skip;
     int temp2 and skip;
     int temp3 and skip;
     int temp4 and skip;
     int die_now and skip;
     int requests_this_child and skip;
     int num_listensocks<==0 and skip;
     void *ptrans and skip;
     void *allocator and skip;
     int status and skip;
     int i and skip;
     int lr and skip;
     void *pollset and skip;
     void *sbh and skip;
     void *bucket_alloc and skip;
     int last_poll_idx and skip;
     int child_num_arg and skip;
     int ap_threads_per_child and skip;
     void *accept_mutex and skip;
     int ap_daemons_to_start<==0 and skip;
     int ap_daemons_min_free<==0 and skip;
     int ap_daemons_max_free<==0 and skip;
     int ap_daemons_limit<==0 and skip;
     int server_limit<==256 and skip;
     int first_server_limit<==0 and skip;
     int changed_limit_at_restart and skip;
     int mpm_state<==1 and skip;
     void *pod and skip;
     int ap_max_daemons_limit<==-1 and skip;
     void *ap_server_conf and skip;
     int one_process<==0 and skip;
     void *pconf and skip;
     void *pchild and skip;
     int ap_my_pid and skip;
     int parent_pid and skip;
     int my_child_num and skip;
     int ap_my_generation<==0 and skip;
     int tpf_child<==0 and skip;
     char *tpf_server_name and skip;
 function getpid ( int RValue )
 {
     frame(getpid_rand_x,return) and ( 
     int return<==0 and skip;
     int getpid_rand_x and skip;
     //getpid_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &getpid_rand_x) and skip
	 }
	 else{
	    getpid_rand_x:=rand(RValue) 
	 };
	 


     return<==1 and RValue:=getpid_rand_x;
     skip
     )
     }; 
  function ap_fatal_signal_child_setup ( int ap_server_conf )
 {
     skip
 };
 function apr_allocator_create ( int *allocator )
 {
     skip
 };
 function apr_allocator_max_free_set ( int allocator,int ap_max_mem_free )
 {
     skip
 };
 function apr_pool_create_ex ( int *pchild,int pconf,int NL,int allocator )
 {
     skip
 };
 function apr_allocator_owner_set ( int allocator,int pchild )
 {
     skip
 };
 function apr_pool_create ( int *ptrans,int pchild )
 {
     skip
 };
 function apr_pool_tag ( int ptrans,char *asdf )
 {
     skip
 };
 function ap_reopen_scoreboard ( int pchild,int NL,int z )
 {
     skip
 };
 function apr_proc_mutex_child_init ( int *accept_mutex,int ap_lock_fname,int pchild,int RValue )
 {
     frame(apr_proc_mutex_child_init_rand_x,return) and ( 
     int return<==0 and skip;
     int apr_proc_mutex_child_init_rand_x and skip;
     //apr_proc_mutex_child_init_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &apr_proc_mutex_child_init_rand_x) and skip
	 }
	 else{
	    apr_proc_mutex_child_init_rand_x:=rand(RValue) 
	 };
	 


     return<==1 and RValue:=apr_proc_mutex_child_init_rand_x;
     skip
     )
     }; 
  function ap_log_error ( int APm,int APe,int status,int ap_server_conf,int a,int b,int c )
 {
     skip
 };
 function ap_log_error5 ( int APm,int APe,int status,int ap_server_conf,int a )
 {
     skip
 };
 function ap_run_child_init ( int pchild,int ap_server_conf )
 {
     skip
 };
 function ap_create_sb_handle ( int *sbh,int pchild,int my_child_num,int z )
 {
     skip
 };
 function ap_update_child_status ( int sbh,int SER,int NL )
 {
     skip
 };
 function apr_pollset_create ( int *pollset,int num_listensocks,int pchild,int z )
 {
     skip
 };
 function apr_pollset_add ( int pollset,int *pfd )
 {
     skip
 };
 function apr_bucket_alloc_create ( int pchild, void* RValue )
 {
     frame(apr_bucket_alloc_create_rand_x,return) and ( 
     int return<==0 and skip;
     int apr_bucket_alloc_create_rand_x and skip;
     //apr_bucket_alloc_create_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &apr_bucket_alloc_create_rand_x) and skip
	 }
	 else{
	    apr_bucket_alloc_create_rand_x:=rand(RValue) 
	 };
	 



     return<==1 and RValue:=(void *)apr_bucket_alloc_create_rand_x;
     skip
     )
     }; 
  function apr_pool_clear ( int ptrans )
 {
     skip
 };
 function apr_pollset_poll ( int pollset,int a,int *numdesc,int *pdesc,int RValue )
 {
     frame(apr_pollset_poll_rand_x,return) and ( 
     int return<==0 and skip;
     int apr_pollset_poll_rand_x and skip;
     //apr_pollset_poll_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &apr_pollset_poll_rand_x) and skip
	 }
	 else{
	    apr_pollset_poll_rand_x:=rand(RValue) 
	 };
	 


     return<==1 and RValue:=apr_pollset_poll_rand_x;
     skip
     )
     }; 
  function ap_run_create_connection ( int ptrans,int ap_server_conf,int csd,int my_child_num,int sbh,int bucket_alloc,int RValue )
 {
     frame(ap_run_create_connection_rand_x,return) and ( 
     int return<==0 and skip;
     int ap_run_create_connection_rand_x and skip;
     //ap_run_create_connection_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &ap_run_create_connection_rand_x) and skip
	 }
	 else{
	    ap_run_create_connection_rand_x:=rand(RValue) 
	 };
	 



     return<==1 and RValue:=ap_run_create_connection_rand_x;
     skip
     )
     }; 
  function ap_process_connection ( int current_conn,int csd )
 {
     skip
 };
 function ap_lingering_close ( int current_conn )
 {
     skip
 };
 function ap_mpm_pod_check ( int a,int RValue )
 {
     frame(ap_mpm_pod_check_rand_x,return) and ( 
     int return<==0 and skip;
     int ap_mpm_pod_check_rand_x and skip;
     //ap_mpm_pod_check_rand_x:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &ap_mpm_pod_check_rand_x) and skip
	 }
	 else{
	    ap_mpm_pod_check_rand_x:=rand(RValue) 
	 };
	 

     return<==1 and RValue:=ap_mpm_pod_check_rand_x;
     skip
     )
     }; 
  function main (  )
 {
     frame(main_3_pfd,main_4_csd,main_4_temp$_1,main_4_8_9_numdesc,main_4_8_9_pdesc,main_4_temp$_2,main_4_rand_x,return,break$,continue) and (
     int continue<==0 and skip;
     int break$<==0 and skip;
     int return<==0 and skip;
     //child_num_arg:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &child_num_arg) and skip
	 }
	 else{
	    child_num_arg:=rand(RValue) 
	 };
	 


     do_ACCEPT:=0;
     die_now:=0;
     last_poll_idx:=0;
     ap_threads_per_child:=0;
     ap_daemons_to_start:=0;
     ap_daemons_min_free:=0;
     ap_daemons_max_free:=0;
     ap_daemons_limit:=0;
     server_limit:=256;
     first_server_limit:=0;
     //ap_listeners:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &ap_listeners) and skip
	 }
	 else{
	    ap_listeners:=rand(RValue) 
	 };
	 



     mpm_state:=9;
     my_child_num:=child_num_arg;
     ap_my_pid:=getpid(RValue);
     requests_this_child:=0;
     ap_fatal_signal_child_setup((int)ap_server_conf);
     apr_allocator_create((int *)&allocator);
     apr_allocator_max_free_set((int)allocator,ap_max_mem_free);
     apr_pool_create_ex((int *)&pchild,(int)pconf,0,(int)allocator);
     apr_allocator_owner_set((int)allocator,(int)pchild);
     apr_pool_create((int *)&ptrans,(int)pchild);
     apr_pool_tag((int)ptrans,"transaction");
     ap_reopen_scoreboard((int)pchild,0,0);
     status:=apr_proc_mutex_child_init((int *)&accept_mutex,ap_lock_fname,(int)pchild,RValue);
     if(status!=7) then 
     {
          fputs("[status!=7]#",fp_executionPath) and skip;
         ap_log_error(3,1,status,(int)ap_server_conf,(int)"Couldn't initialize cross-process lock in child (%s) (%d)",ap_lock_fname,ap_accept_lock_mech);
         clean_child_exit(1,RValue)
         
     }
     else 
     {
          fputs("[!(status!=7)]#",fp_executionPath) and skip 
     };
     temp1:=unixd_setup_child(RValue);
     if(temp1!=0) then 
     {
          fputs("[temp1!=0]#",fp_executionPath) and skip;
         clean_child_exit(1,RValue)
         
     }
     else 
     {
          fputs("[!(temp1!=0)]#",fp_executionPath) and skip 
     };
     ap_run_child_init((int)pchild,(int)ap_server_conf);
     ap_create_sb_handle((int *)&sbh,(int)pchild,my_child_num,0);
     ap_update_child_status((int)sbh,1,0);
     //apr_pollset_create((int *)&pollset,num_listensocks,(int)pchild,0) and skip;
     //num_listensocks:=rand(RValue);
	 if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &num_listensocks) and skip
	 }
	 else{
	    num_listensocks:=rand(RValue) 
	 };

     lr:=ap_listeners;
     i:=num_listensocks;
     while( i!=0)
     {
          fputs("[i!=0]#" ,fp_executionPath ) and skip;
         i:=i-1;
         int main_3_pfd<==0 and skip;
         pfd_desc_type:=6;
         pfd_desc_s:=1;
         pfd_reqevents:=5;
         pfd_client_data:=lr;
         apr_pollset_add((int)pollset,&main_3_pfd) 
     };
     fputs("[!(i!=0)]#",fp_executionPath) and skip ;
     i:=i-1;
     mpm_state:=8;
     bucket_alloc:=apr_bucket_alloc_create((int)pchild,RValue);
     break$<==0 and skip;
     while( return=0 AND   break$=0 AND   !die_now)
     {
          fputs("[!die_now]#" ,fp_executionPath ) and skip;
         continue<==0 and skip;
         conn_rec*current_conn and skip;
         void *main_4_csd<==0 and skip;
         apr_pool_clear((int)ptrans);
         if(ap_max_requests_per_child>0) then 
         {
              fputs("[ap_max_requests_per_child>0]#",fp_executionPath) and skip;
             if(requests_this_child>=ap_max_requests_per_child) then 
             {
                  fputs("[requests_this_child>=ap_max_requests_per_child]#",fp_executionPath) and skip;
                 requests_this_child:=requests_this_child+1;
                 clean_child_exit(0,RValue)
                 
             }
             else 
             {
                  fputs("[!(requests_this_child>=ap_max_requests_per_child)]#",fp_executionPath) and skip 
             };
             requests_this_child:=requests_this_child+1
             
         }
         else 
         {
              fputs("[!(ap_max_requests_per_child>0)]#",fp_executionPath) and skip 
         };
         //ap_update_child_status((int)sbh,1,0) and skip;
         int main_4_temp$_1 and skip;
         main_4_temp$_1:=accept_mutex_on(RValue);
         SAFE_ACCEPT(main_4_temp$_1,RValue);
         do_ACCEPT:=1;
         do_ACCEPT:=0;
         if(num_listensocks=1) then 
         {
              fputs("[num_listensocks==1]#",fp_executionPath) and skip;
             lr:=ap_listeners
             
         }
         else
         { 
          fputs("[!(num_listensocks==1)]#",fp_executionPath) and skip;
         while(break$=0 AND return=0 AND  1)
         {
              fputs("[1]#",fp_executionPath) and skip;
             continue<==0 and skip;
             int main_4_8_9_numdesc and skip;
             void *main_4_8_9_pdesc and skip;
             status:=apr_pollset_poll((int)pollset,-1,&main_4_8_9_numdesc,(int *)&main_4_8_9_pdesc,RValue);
             if(status!=7) then 
             {
                  fputs("[status!=7]#",fp_executionPath) and skip;
                 temp2:=APR_STATUS_IS_EINTR(status,RValue);
                 if(temp2!=0) then 
                 {
                      fputs("[temp2!=0]#",fp_executionPath) and skip;
                     if(one_process!=0) then 
                     {
                          fputs("[one_process!=0]#",fp_executionPath) and skip;
                         if(shutdown_pending!=0) then 
                         {
                              fputs("[shutdown_pending!=0]#",fp_executionPath) and skip;
                              return<==1 and skip
                             
                         }
                         else 
                         {
                              fputs("[!(shutdown_pending!=0)]#",fp_executionPath) and skip
                         }
                         
                     }
                     else 
                     {
                          fputs("[!(one_process!=0)]#",fp_executionPath) and skip 
                     };
                     if(return=0)  then
                     {
                         continue<==1 and skip
                      }
                     else
                     {
                         skip
                     }
                     
                 }
                 else 
                 {
                      fputs("[!(temp2!=0)]#",fp_executionPath) and skip 
                 };
                 if(continue=0)   then 
                 {
                     if(return=0)  then
                     {
                         ap_log_error5(3,2,status,(int)ap_server_conf,(int)"apr_pollset_poll: (listen)");
                         clean_child_exit(1,RValue)
                     }
                     else
                     {
                         skip
                     }
                 }
                 else
                 {
                     skip
                 }
                 
             }
             else 
             {
                  fputs("[!(status!=7)]#",fp_executionPath) and skip 
             };
             if(continue=0)  then
             {
                 if(return=0)  then
                 {
                     if(last_poll_idx>=main_4_8_9_numdesc) then 
                     {
                          fputs("[last_poll_idx>=numdesc]#",fp_executionPath) and skip;
                         last_poll_idx:=0
                     }
                     else 
                     {
                          fputs("[!(last_poll_idx>=numdesc)]#",fp_executionPath) and skip 
                     };
                     lr:=1;
                     break$<==1 and skip
                  }
                 else
                 {
                     skip
                 }
             }
             else
             {
                 skip
             }
         };
         continue<==0 and skip;
         fputs("[!(1)]#",fp_executionPath) and skip
     };
     if(break$=0)   then 
     {
         if(return=0)  then
         {
             //status:=rand(RValue);
	if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &status) and skip
	 }
	 else{
	    status:=rand(RValue) 
	 };


             int main_4_temp$_2 and skip;
             main_4_temp$_2:=accept_mutex_off(RValue);
             SAFE_ACCEPT(main_4_temp$_2,RValue);
             if(status=4) then 
             {
                  fputs("[status==4]#",fp_executionPath) and skip;
                 clean_child_exit(1,RValue)
                 
             }
             else
             { 
              fputs("[!(status==4)]#",fp_executionPath) and skip;
             if(status!=7) then 
             {
                  fputs("[status!=7]#",fp_executionPath) and skip;
                 continue<==1 and skip
                  
             }
             else 
             {
                  fputs("[!(status!=7)]#",fp_executionPath) and skip
             }
         };
         if(continue=0)  then 
         {
             current_conn:=ap_run_create_connection((int)ptrans,(int)ap_server_conf,(int)main_4_csd,my_child_num,(int)sbh,(int)bucket_alloc,RValue);
             if(current_conn!=0) then 
             {
                  fputs("[current_conn!=0]#",fp_executionPath) and skip;
                 ap_process_connection(current_conn,(int)main_4_csd);
                 ap_lingering_close(current_conn)
                 
             }
             else 
             {
                  fputs("[!(current_conn!=0)]#",fp_executionPath) and skip 
             };
             int main_4_rand_x and skip;
             //main_4_rand_x:=rand(RValue);
	if(!feof(fp_values))then{
	     fscanf(fp_values,"%d", &main_4_rand_x) and skip
	 }
	 else{
	    main_4_rand_x:=rand(RValue) 
	 };


             temp3:=ap_mpm_pod_check((int)pod,RValue);
             if(temp3=7) then 
             {
                  fputs("[temp3==7]#",fp_executionPath) and skip;
                 die_now:=1
             }
             else
             {
                  fputs("[!(temp3==7)]#",fp_executionPath) and skip;
                 if(ap_my_generation!=main_4_rand_x) then 
                 {
                      fputs("[ap_my_generation!=rand_x]#",fp_executionPath) and skip;
                     die_now:=1
                     
                 }
                 else 
                 {
                      fputs("[!(ap_my_generation!=rand_x)]#",fp_executionPath) and skip
                 }
             }
         }
         else
         {
             skip
         }
     }
     else
     {
         skip
     }
 }
 else
 {
     skip
 }
 };
 break$<==0 and skip;
 continue<==0 and skip;
 fputs("[!(!die_now)]#",fp_executionPath) and skip ;
 if(return=0)   then 
 {
     clean_child_exit(0,RValue);
     0 
 }
 else
 {
     skip
 }
 )
 };
  main();
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
