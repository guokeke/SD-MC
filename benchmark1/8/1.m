frame(fp_executionPath,fp_values,last_copy_time,curtime,got_SIGHUP,wakend) and (
FILE* fp_executionPath <==fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;


int last_copy_time<==0 and skip;
int curtime and skip;
int got_SIGHUP and skip;
int wakend and skip;
 
 
 function init (  )
 {
     wakend:=1;
	 //got_SIGHUP:=1
     //got_SIGHUP:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &got_SIGHUP) and skip
	 }
	 else
	 {
	    got_SIGHUP:=rand(RValue)
	 }
	 //output("got_SIGHUP=", got_SIGHUP, "\n") and skip     
 };
 function ProcessConfigFile ( int a )
 {
     skip
 };
 function XLogArchivingActive ( int RValue )
 {
     frame(XLogArchivingActive_rand_x,return) and ( 
     int return<==0 and skip;
     int XLogArchivingActive_rand_x and skip;
	 //XLogArchivingActive_rand_x:=1;
     //XLogArchivingActive_rand_x:=rand(RValue);
	 if(!feof(fp_values)) then{
	     fscanf(fp_values, "%d", &XLogArchivingActive_rand_x) and skip
	 }
	 else{
	     XLogArchivingActive_rand_x:=rand(RValue)
	 };
	 
	 //output("XLogArchivingActive_rand_x=", XLogArchivingActive_rand_x, "\n") and skip;
     return<==1 and RValue:=XLogArchivingActive_rand_x;
     skip
     )
 }; 
  function pgarch_ArchiverCopyLoop (  )
 {
     skip
 };
 function mytime ( int a,int RValue )
 {
     frame(time_rand_x,return) and ( 
     int return<==0 and skip;
     int time_rand_x and skip;
	 //time_rand_x:=1;
     //time_rand_x:=rand(RValue);
	 if(!feof(fp_values)) then{
	     fscanf(fp_values, "%d", &time_rand_x) and skip
	 }
	 else
	 {
	     time_rand_x:=rand(RValue)
	 };
	 //output("time_rand_x=", time_rand_x, "\n") and skip;
     return<==1 and RValue:=time_rand_x;
     skip
     )
     }; 
  function pg_usleep ( int a )
 {
     skip
 };
 function PostmasterIsAlive ( int a,int RValue )
 {
     frame(PostmasterIsAlive_rand_x,return) and ( 
     int return<==0 and skip;
     int PostmasterIsAlive_rand_x and skip;
	 //PostmasterIsAlive_rand_x:=1;
     //PostmasterIsAlive_rand_x:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &PostmasterIsAlive_rand_x) and skip
	 }
	 else
	 {
	    PostmasterIsAlive_rand_x:=rand(RValue)
	 };
	 //output("PostmasterIsAlive_rand_x=", PostmasterIsAlive_rand_x, "\n") and skip;
     return<==1 and RValue:=PostmasterIsAlive_rand_x;
     skip
     )
  }; 
  function main (  )
 {
     frame(main_1_2_rand_1, 1000,main_1_temp_1,count$,break$) and (
     int break$<==0 and skip;
     init();
     wakend:=1;
     int count$<==0 and skip;
     break$<==0 and skip;
	 int main_1_temp_1<==1 and skip;
     while( break$=0 AND  count$=0 OR main_1_temp_1!=0)
     {
         main_1_temp_1:=PostmasterIsAlive(1,RValue);
		 count$:=count$+1;
         if(got_SIGHUP) then 
         {
              fputs("[got_SIGHUP]\n",fp_executionPath) and skip;
             got_SIGHUP:=0;
             ProcessConfigFile(1);
             int main_1_2_rand_1 and skip;
             main_1_2_rand_1:=XLogArchivingActive(RValue);
             if(!main_1_2_rand_1) then 
             {
                  fputs("[!rand_1]\n",fp_executionPath) and skip;
                 break$<==1 and skip
              }
             else 
             {
                  fputs("[!(!rand_1)]\n",fp_executionPath) and skip
             }
             
         }
         else 
         {
              fputs("[!(got_SIGHUP)]\n",fp_executionPath) and skip 
         };
         
		 
		 if(break$=0)   then 
         {
             if(wakend!=0) then 
             {
                  fputs("[wakend!=0]\n",fp_executionPath) and skip;
                 wakend:=0;
                 pgarch_ArchiverCopyLoop();
                 last_copy_time:=mytime(0,RValue)
                 
             }
             else 
             {
                  fputs("[!(wakend!=0)]\n",fp_executionPath) and skip 
             };
             if(!wakend) then 
             {
                  fputs("[!wakend]\n",fp_executionPath) and skip;
                 pg_usleep(1000*1000000);
                 curtime:=mytime(0,RValue);
                 int temp1<==(unsigned int)(curtime-last_copy_time) and skip;
                 int temp2<==(unsigned int)1000 and skip;
                 if(temp1>=temp2) then 
                 {
                      fputs("[temp1>=temp2]\n",fp_executionPath) and skip;
                     wakend:=1
                     
                 }
                 else 
                 {
                      fputs("[!(temp1>=temp2)]\n",fp_executionPath) and skip
                 }
                 
             }
             else 
             {
                  fputs("[!(!wakend)]\n",fp_executionPath) and skip 
             }

            
         }
         else
         {
             skip
         }
     };
     break$<==0 and skip
     )
 };
 main();
     fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
