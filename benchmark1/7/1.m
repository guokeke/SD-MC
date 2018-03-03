frame(fp_executionPath,file,closed,MaxBackends,family,hostName,portNumber,unixSocketName,MaxListen,fd,err,maxconn,one,ret,service,hint,listen_index,added,addr_ai_family,addr,MAXADDR,ListenSocket_OF_listen_index,sock_path,addrs) and (
FILE* fp_executionPath <==fopen("executionPath.txt", "w") and skip;


FILE * file <== freopen("values.txt", "r", stdin) and skip;
int closed and skip;
int MaxBackends and skip;
int family and skip;
char *hostName and skip;
int portNumber and skip;
char *unixSocketName and skip;
int MaxListen and skip;
int fd,err and skip;
int maxconn and skip;
int one and skip;
int ret and skip;
char *service and skip;
int hint and skip;
int listen_index and skip;
int added and skip;
int addr_ai_family and skip;
int addr and skip;
int MAXADDR and skip;
int ListenSocket_OF_listen_index and skip;
char *sock_path and skip;
int addrs and skip;
 function main (  )
 {
     frame(main_3_rand_x,main_3_rand_x1,main_3_rand_x2,main_3_16_rand_x3,main_3_rand_x4,main_3_18_rand_x5,main_3_21_rand_x6,goto,break$) and (
     int break$<==0 and skip;
     int goto<==0 and skip;
     one:=1;
     listen_index:=0;
     added:=0;
     //MAXADDR:=rand(RValue);
	 scanf("%d", &MAXADDR) and skip;
     //addrs:=rand(RValue);
	 scanf("%d", &addrs) and skip;
     //MaxBackends:=rand(RValue);
	 scanf("%d", &MaxBackends) and skip;
     //ret:=rand(RValue);
	 scanf("%d", &ret) and skip;
     if(family=3) then 
     {
          fputs("[family==3]#",fp_executionPath) and skip;
         service:=sock_path
         
     }
     else
     { 
      fputs("[!(family==3)]#",fp_executionPath) and skip;
     service:=(char *)1
 };
 addr:=addrs;
 break$<==0 and skip;
 while( break$=0 AND   addr<MAXADDR)
 {
      fputs("[addr<MAXADDR]#" ,fp_executionPath ) and skip;
     int main_3_rand_x and skip;
     //main_3_rand_x:=rand(RValue);
	 scanf("%d", &main_3_rand_x) and skip;
     int main_3_rand_x1 and skip;
     //main_3_rand_x1:=rand(RValue);
	 scanf ("%d", &main_3_rand_x1) and skip;
     if(!main_3_rand_x) then 
     {
          fputs("[!rand_x]#",fp_executionPath) and skip;
         if(main_3_rand_x1) then 
         {
              fputs("[rand_x1]#",fp_executionPath) and skip;
             goto<==1 and skip
             
         }
         else 
         {
              fputs("[!(rand_x1)]#",fp_executionPath) and skip
         }
         
     }
     else 
     {
          fputs("[!(!rand_x)]#",fp_executionPath) and skip 
     };
     if(goto=0)   then 
     {
         break$<==0 and skip;
         while( break$=0 AND   listen_index<MaxListen)
         {
              fputs("[listen_index<MaxListen]#" ,fp_executionPath ) and skip;
             if(ListenSocket_OF_listen_index=-1) then 
             {
                  fputs("[ListenSocket_OF_listen_index==-1]#",fp_executionPath) and skip;
                 break$<==1 and skip
              }
             else 
             {
                  fputs("[!(ListenSocket_OF_listen_index==-1)]#",fp_executionPath) and skip 
             };
             if(break$=0)   then
             {
                 listen_index:=listen_index+1
             }
             else
             {
                 skip
             }
         };
         break$<==0 and skip;
         fputs("[!(listen_index<MaxListen)]#",fp_executionPath) and skip ;
         if(listen_index>=MaxListen) then 
         {
              fputs("[listen_index>=MaxListen]#",fp_executionPath) and skip;
             break$<==1 and skip
              
         }
         else 
         {
              fputs("[!(listen_index>=MaxListen)]#",fp_executionPath) and skip 
         };
         if(break$=0)   then
         {
             if(addr_ai_family=1) then 
             {
                  fputs("[addr_ai_family==1]#",fp_executionPath) and skip;
                 skip
                 
             }
             else
             { 
              fputs("[!(addr_ai_family==1)]#",fp_executionPath) and skip;
             if(addr_ai_family=2) then 
             {
                  fputs("[addr_ai_family==2]#",fp_executionPath) and skip;
                 skip
             }
             else
             {
                  fputs("[!(addr_ai_family==2)]#",fp_executionPath) and skip;
                 if(addr_ai_family=3) then 
                 {
                      fputs("[addr_ai_family==3]#",fp_executionPath) and skip;
                     skip
                 }
                 else
                 {
                      fputs("[!(addr_ai_family==3)]#",fp_executionPath) and skip;
                     skip
                 }
             }
         };
         //fd:=rand(RValue);
		 scanf("%d", &fd) and skip;
         if(fd) then 
         {
              fputs("[fd]#",fp_executionPath) and skip;
             goto<==1 and skip
             
         }
         else 
         {
              fputs("[!(fd)]#",fp_executionPath) and skip 
         };
         if(goto=0)   then 
         {
             int main_3_rand_x2 and skip;
             //main_3_rand_x2:=rand(RValue);
			 scanf("%d", &main_3_rand_x2) and skip;
             if(main_3_rand_x2) then 
             {
                  fputs("[rand_x2]#",fp_executionPath) and skip;
                 int main_3_16_rand_x3 and skip;
                 //main_3_16_rand_x3:=rand(RValue);
				 scanf("%d", &main_3_16_rand_x3) and skip;
                 if(main_3_16_rand_x3) then 
                 {
                      fputs("[rand_x3]#",fp_executionPath) and skip;
                     goto<==1 and skip
                     
                 }
                 else 
                 {
                      fputs("[!(rand_x3)]#",fp_executionPath) and skip
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
          fputs("[!(rand_x2)]#",fp_executionPath) and skip 
     };
     if(goto=0)   then 
     {
         int main_3_rand_x4 and skip;
         //main_3_rand_x4:=rand(RValue);
		 scanf("%d", &main_3_rand_x4) and skip;
         if(main_3_rand_x4) then 
         {
              fputs("[rand_x4]#",fp_executionPath) and skip;
             int main_3_18_rand_x5 and skip;
             //main_3_18_rand_x5:=rand(RValue);
			 scanf("%d", &main_3_18_rand_x5) and skip;
             if(main_3_18_rand_x5) then 
             {
                  fputs("[rand_x5]#",fp_executionPath) and skip;
                 closed:=1;
                 goto<==1 and skip
                 
             }
             else 
             {
                  fputs("[!(rand_x5)]#",fp_executionPath) and skip
             }
         }
         else
         {
             skip
         }
         
     }
     else 
     {
          fputs("[!(rand_x4)]#",fp_executionPath) and skip 
     };
     if(goto=0)   then 
     {
         //err:=rand(RValue);
		 scanf("%d", &err) and skip;
         if(err<0) then 
         {
              fputs("[err<0]#",fp_executionPath) and skip;
             closed:=1;
             goto<==1 and skip
             
         }
         else 
         {
              fputs("[!(err<0)]#",fp_executionPath) and skip 
         };
         if(goto=0)   then 
         {
             if(addr_ai_family=3) then 
             {
                  fputs("[addr_ai_family==3]#",fp_executionPath) and skip;
                 int main_3_21_rand_x6 and skip;
                 //main_3_21_rand_x6:=rand(RValue);
				 scanf("%d", &main_3_21_rand_x6) and skip;
                 if(main_3_21_rand_x6!=1) then 
                 {
                      fputs("[rand_x6!=1]#",fp_executionPath) and skip;
                     closed:=1;
                     break$<==1 and skip
                      
                 }
                 else 
                 {
                      fputs("[!(rand_x6!=1)]#",fp_executionPath) and skip
                 }
                 
             }
             else 
             {
                  fputs("[!(addr_ai_family==3)]#",fp_executionPath) and skip 
             };
             if(break$=0)   then 
             {
                 maxconn:=MaxBackends*2;
                 if(maxconn>10) then 
                 {
                      fputs("[maxconn>10]#",fp_executionPath) and skip;
                     maxconn:=10
                 }
                 else 
                 {
                      fputs("[!(maxconn>10)]#",fp_executionPath) and skip 
                 };
                 //err:=rand(RValue);
				 scanf("%d", &err) and skip;
                 if(err<0) then 
                 {
                      fputs("[err<0]#",fp_executionPath) and skip;
                     closed:=1;
                     goto<==1 and skip
                     
                 }
                 else 
                 {
                      fputs("[!(err<0)]#",fp_executionPath) and skip 
                 };
                 if(goto=0)   then 
                 {
                     ListenSocket_OF_listen_index:=fd;
                     added:=added+1;
                     if(1) then 
                     {
                          fputs("[1]#",fp_executionPath) and skip;
                         goto<==0 and skip;
                         0 
                         
                     }
                     else 
                     {
                          fputs("[!(1)]#",fp_executionPath) and skip 
                     };
                     addr:=addr+1
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
 fputs("[!(addr<MAXADDR)]#",fp_executionPath) and skip ;
 if(!added) then 
 {
      fputs("[!added]#",fp_executionPath) and skip;
     ret:=0
     
 }
 else 
 {
      fputs("[!(!added)]#",fp_executionPath) and skip 
 };
 ret:=0
 )
 };
  main();
   fclose(fp_executionPath) and skip;
  fclose(file) and skip
 )
