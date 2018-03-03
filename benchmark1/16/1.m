frame(fp_executionPath,fp_values,Stored) and (
FILE* fp_executionPath <==fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;
int Stored and skip;
 function init (  )
 {
     Stored:=0
     
 };
 function callback (  )
 {
     skip
 };
 function IoQueueWorkItem (  )
 {
     skip
 };
 function main (  )
 {
     frame(main_rand_x,main_1_rand_x1,break$) and (
     int break$<==0 and skip;
     int main_rand_x and skip;
     //main_rand_x:=rand(RValue);
	 if(!feof(fp_values))then
	 {
	    fscanf(fp_values, "%d", &main_rand_x) and skip
	 }
	 else
	 {
	    main_rand_x:=rand(RValue)
	 };

     break$<==0 and skip;
     while( break$=0 AND   main_rand_x!=0)
     {
          fputs("[rand_x!=0]#" ,fp_executionPath ) and skip;
         int main_1_rand_x1 and skip;
         //main_1_rand_x1:=rand(RValue);
		  if(!feof(fp_values))then
	      {
	         fscanf(fp_values, "%d", &main_1_rand_x1) and skip
	      }
	      else
	      {
	         main_1_rand_x1:=rand(RValue)
	      };

         if(main_1_rand_x1!=0) then 
         {
              fputs("[rand_x1!=0]#",fp_executionPath) and skip;
             callback()
             
         }
         else
         { 
          fputs("[!(rand_x1!=0)]#",fp_executionPath) and skip;
         IoQueueWorkItem();
         Stored:=1;
         break$<==1 and skip
      };
     if(break$=0)   then 
     {
         //main_rand_x:=rand(RValue)
		  if(!feof(fp_values))then
	      {
	         fscanf(fp_values, "%d", &main_rand_x) and skip
	      }
	      else
	      {
	         main_rand_x:=rand(RValue)
	      }
     }
     else
     {
         skip
     }
 };
 break$<==0 and skip;
 fputs("[!(rand_x!=0)]#",fp_executionPath) and skip ;
 if(Stored=1) then 
 {
      fputs("[Stored==1]#",fp_executionPath) and skip;
     callback();
     Stored:=0
     
 }
 else 
 {
      fputs("[!(Stored==1)]#",fp_executionPath) and skip
 }
 )
 };
  main();
    fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
