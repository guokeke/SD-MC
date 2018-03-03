frame(fp_executionPath,fp_values,WarmPollPeriod,status,polling,PowerStateIsAC) and (
FILE* fp_executionPath <==fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int WarmPollPeriod and skip;
int status and skip;
int polling and skip;
int PowerStateIsAC and skip;
 function ExAcquireFastMutex (  )
 {
     skip
 };
 function ExReleaseFastMutex (  )
 {
     skip
 };
 function main ( int RValue )
 {
     frame(main_1_rand_x,main_1_5_rand_x1,main_1_5_6_timeOut1,main_1_5_6_status,main_1_5_6_deviceStatus,main_1_5_6_devId,main_1_5_6_requestRescan,main_1_5_6_pollingFailureThreshold,main_1_5_6_7_rand_x2,main_1_5_6_7_12_rand_x3,main_1_5_6_7_12_13_rand_x3,main_1_5_6_7_12_13_14_rand_x4,main_1_5_6_7_12_13_14_16_17_mfg,main_1_5_6_7_12_13_14_16_17_mdl,main_1_5_6_7_12_13_14_16_17_cls,main_1_5_6_7_12_13_14_16_17_des,main_1_5_6_7_12_13_14_16_17_aid,main_1_5_6_7_12_13_14_16_17_cid,main_1_5_6_7_12_13_14_16_22_rand_x5,main_1_5_6_7_ddd,count$,goto,break$) and (
     int break$<==0 and skip;
     int goto<==0 and skip;
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &WarmPollPeriod) and skip
	 }
	 else{
        WarmPollPeriod:=rand(RValue)
	 };
     //status:=rand(RValue);
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &status) and skip
	 }
	 else{
        status:=rand(RValue)
	 };

     //polling:=rand(RValue);
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &polling) and skip
	 }
	 else{
        polling:=rand(RValue)
	 };

     //PowerStateIsAC:=rand(RValue);
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &PowerStateIsAC) and skip
	 }
	 else{
        PowerStateIsAC:=rand(RValue)
	 };

     if(status>0) then 
     {
          fputs("[status>0]#",fp_executionPath) and skip;
         ExAcquireFastMutex();
         rand(RValue) and skip;
         ExReleaseFastMutex();
         //WarmPollPeriod:=rand(RValue);
		  if(!feof(fp_values))then{
	          fscanf(fp_values, "%d", &WarmPollPeriod) and skip
	      }
	      else{
              WarmPollPeriod:=rand(RValue)
	      };

         if(WarmPollPeriod<5) then 
         {
              fputs("[WarmPollPeriod<5]#",fp_executionPath) and skip;
             WarmPollPeriod:=5
             
         }
         else
         { 
          fputs("[!(WarmPollPeriod<5)]#",fp_executionPath) and skip;
         if(WarmPollPeriod>20) then 
         {
              fputs("[WarmPollPeriod>20]#",fp_executionPath) and skip;
             WarmPollPeriod:=20
             
         }
         else 
         {
              fputs("[!(WarmPollPeriod>20)]#",fp_executionPath) and skip
         }
     };
     int main_1_rand_x and skip;
     //main_1_rand_x:=rand(RValue);
	  if(!feof(fp_values))then{
	       fscanf(fp_values, "%d", &main_1_rand_x) and skip
	  }
	  else{
           main_1_rand_x:=rand(RValue)
	  };

     if(main_1_rand_x!=0) then 
     {
          fputs("[rand_x!=0]#",fp_executionPath) and skip;
         polling:=1;
         int main_1_5_rand_x1 and skip;
         //main_1_5_rand_x1:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_1_5_rand_x1) and skip
	      }
	      else{
             main_1_5_rand_x1:=rand(RValue)
	      };

         if(main_1_5_rand_x1!=0) then 
         {
              fputs("[rand_x1!=0]#",fp_executionPath) and skip;
             int main_1_5_6_timeOut1 and skip;
             int main_1_5_6_status and skip;
             int main_1_5_6_deviceStatus and skip;
             int main_1_5_6_devId and skip;
             int main_1_5_6_requestRescan and skip;
             int main_1_5_6_pollingFailureThreshold<==10 and skip;
             int count$<==0 and skip;
             break$<==0 and skip;
             while( break$=0 AND   ( count$=0 OR 1))
             {
                 count$:=count$+1;
                 if(PowerStateIsAC!=0) then 
                 {
                      fputs("[PowerStateIsAC!=0]#",fp_executionPath) and skip;
                     skip
                     
                 }
                 else
                 { 
                  fputs("[!(PowerStateIsAC!=0)]#",fp_executionPath) and skip;
                 skip
             };
             //main_1_5_6_status:=rand(RValue);
			  if(!feof(fp_values))then{
	              fscanf(fp_values, "%d", &main_1_5_6_status) and skip
	          }
	          else{
                  main_1_5_6_status:=rand(RValue)
	          };


             int main_1_5_6_7_rand_x2 and skip;
             //main_1_5_6_7_rand_x2:=rand(RValue);
			  if(!feof(fp_values))then{
	              fscanf(fp_values, "%d", &main_1_5_6_7_rand_x2) and skip
	          }
	          else{
                  main_1_5_6_7_rand_x2:=rand(RValue)
	          };

             if(main_1_5_6_7_rand_x2!=0) then 
             {
                  fputs("[rand_x2!=0]#",fp_executionPath) and skip;
                 break$<==1 and skip
                  
             }
             else 
             {
                  fputs("[!(rand_x2!=0)]#",fp_executionPath) and skip 
             };
             if(break$=0)   then
             {
                 if(!PowerStateIsAC) then 
                 {
                      fputs("[!PowerStateIsAC]#",fp_executionPath) and skip;
                     goto<==1 and skip
                     
                 }
                 else 
                 {
                      fputs("[!(!PowerStateIsAC)]#",fp_executionPath) and skip 
                 };
                 if(goto=0)   then 
                 {
                     if(-1=main_1_5_6_status) then 
                     {
                          fputs("[-1==status]#",fp_executionPath) and skip;
                         int main_1_5_6_7_12_rand_x3 and skip;
                         //main_1_5_6_7_12_rand_x3:=rand(RValue);
						  if(!feof(fp_values))then{
            	              fscanf(fp_values, "%d", &main_1_5_6_7_12_rand_x3) and skip
	                      }
	                      else{
                              main_1_5_6_7_12_rand_x3:=rand(RValue)
	                      };


                         if(main_1_5_6_7_12_rand_x3!=0) then 
                         {
                              fputs("[rand_x3!=0]#",fp_executionPath) and skip;
                             int main_1_5_6_7_12_13_rand_x3 and skip;
                             //main_1_5_6_7_12_13_rand_x3:=rand(RValue);
							 if(!feof(fp_values))then{
            	                 fscanf(fp_values, "%d", &main_1_5_6_7_12_13_rand_x3) and skip
	                         }
	                         else{
                                 main_1_5_6_7_12_13_rand_x3:=rand(RValue)
	                         };

                             if(main_1_5_6_7_12_13_rand_x3!=0) then 
                             {
                                  fputs("[rand_x3!=0]#",fp_executionPath) and skip;
                                 main_1_5_6_requestRescan:=0;
                                 //main_1_5_6_deviceStatus:=rand(RValue);
								  if(!feof(fp_values))then{
            	                      fscanf(fp_values, "%d", &main_1_5_6_deviceStatus) and skip
	                              }
	                              else{
                                      main_1_5_6_deviceStatus:=rand(RValue)
	                              };


                                 int main_1_5_6_7_12_13_14_rand_x4 and skip;
                                 //main_1_5_6_7_12_13_14_rand_x4:=rand(RValue);
								 if(!feof(fp_values))then{
            	                      fscanf(fp_values, "%d", &main_1_5_6_7_12_13_14_rand_x4) and skip
	                              }
	                              else{
                                      main_1_5_6_7_12_13_14_rand_x4:=rand(RValue)
	                              };


                                 if(main_1_5_6_7_12_13_14_rand_x4!=0) then 
                                 {
                                      fputs("[rand_x4!=0]#",fp_executionPath) and skip;
                                     skip
                                     
                                 }
                                 else
                                 { 
                                  fputs("[!(rand_x4!=0)]#",fp_executionPath) and skip;
                                 //main_1_5_6_devId:=rand(RValue);
								  if(!feof(fp_values))then{
            	                      fscanf(fp_values, "%d", &main_1_5_6_devId) and skip
	                              }
	                              else{
                                      main_1_5_6_devId:=rand(RValue)
	                              };

                                 if(main_1_5_6_devId!=0) then 
                                 {
                                      fputs("[devId!=0]#",fp_executionPath) and skip;
                                     int main_1_5_6_7_12_13_14_16_17_mfg<==0,main_1_5_6_7_12_13_14_16_17_mdl<==0,main_1_5_6_7_12_13_14_16_17_cls,main_1_5_6_7_12_13_14_16_17_des,main_1_5_6_7_12_13_14_16_17_aid,main_1_5_6_7_12_13_14_16_17_cid and skip;
                                     rand(RValue) and skip;
                                     if(main_1_5_6_7_12_13_14_16_17_mfg!=0) then 
                                     {
                                          fputs("[mfg!=0]#",fp_executionPath) and skip;
                                         if(main_1_5_6_7_12_13_14_16_17_mdl!=0) then 
                                         {
                                              fputs("[mdl!=0]#",fp_executionPath) and skip;
                                             main_1_5_6_requestRescan:=1
                                             
                                         }
                                         else 
                                         {
                                              fputs("[!(mdl!=0)]#",fp_executionPath) and skip
                                         }
                                         
                                     }
                                     else 
                                     {
                                          fputs("[!(mfg!=0)]#",fp_executionPath) and skip
                                     }
                                     
                                 }
                                 else
                                 { 
                                  fputs("[!(devId!=0)]#",fp_executionPath) and skip;
                                 skip
                             };
                             if(main_1_5_6_requestRescan!=0) then 
                             {
                                  fputs("[requestRescan!=0]#",fp_executionPath) and skip;
                                 skip
                             }
                             else
                             {
                                  fputs("[!(requestRescan!=0)]#",fp_executionPath) and skip;
                                 int main_1_5_6_7_12_13_14_16_22_rand_x5 and skip;
                                 //main_1_5_6_7_12_13_14_16_22_rand_x5:=rand(RValue);
								 if(!feof(fp_values))then{
            	                      fscanf(fp_values, "%d", &main_1_5_6_7_12_13_14_16_22_rand_x5) and skip
	                              }
	                              else{
                                      main_1_5_6_7_12_13_14_16_22_rand_x5:=rand(RValue)
	                              };
                                 if(main_1_5_6_7_12_13_14_16_22_rand_x5!=0) then 
                                 {
                                      fputs("[rand_x5!=0]#",fp_executionPath) and skip;
                                     skip
                                     
                                 }
                                 else 
                                 {
                                      fputs("[!(rand_x5!=0)]#",fp_executionPath) and skip
                                 }
                             }
                         };
                         rand(RValue) and skip;
                         if(main_1_5_6_requestRescan!=0) then 
                         {
                              fputs("[requestRescan!=0]#",fp_executionPath) and skip;
                             rand(RValue) and skip
                             
                         }
                         else 
                         {
                              fputs("[!(requestRescan!=0)]#",fp_executionPath) and skip
                         }
                     }
                     else
                     {
                          fputs("[!(rand_x3!=0)]#",fp_executionPath) and skip;
                         skip
                     }
                 }
                 else
                 {
                      fputs("[!(rand_x3!=0)]#",fp_executionPath) and skip;
                     skip
                 }
                 
             }
             else 
             {
                  fputs("[!(-1==status)]#",fp_executionPath) and skip 
             };
             goto<==0 and skip;
             int main_1_5_6_7_ddd<==0 and skip;
             main_1_5_6_7_ddd:=main_1_5_6_7_ddd
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
 if(goto=0)   then 
 {
     polling:=0
 }
 else
 {
     skip
 }
 }
 else
 {
      fputs("[!(rand_x1!=0)]#",fp_executionPath) and skip;
     polling:=0
 }
 }
 else
 {
      fputs("[!(rand_x!=0)]#",fp_executionPath) and skip;
     skip
 }
 
 }
 else 
 {
      fputs("[!(status>0)]#",fp_executionPath) and skip 
 };
 polling:=1
 )
 };
  main(RValue);
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
