frame(fp_executionPath,fp_values,WItemsNum) and (
FILE* fp_executionPath <==fopen("D:\\D\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\D\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;
int WItemsNum and skip;
 function callback1 (  )
 {
     skip
 };
 function callback2 (  )
 {
     skip
 };
 function main (  )
 {
     frame(main_rand_x,break$) and (
     int break$<==0 and skip;
     //WItemsNum:=rand(RValue);
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &WItemsNum) and skip
	 }
	 else{
	    WItemsNum:=rand(RValue)
	 };

     int main_rand_x and skip;
     //main_rand_x:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &main_rand_x) and skip
	 }
	 else{
	    main_rand_x:=rand(RValue)
	 };


     break$<==0 and skip;
    
          fputs("[1]#" ,fp_executionPath ) and skip;
         if(!(WItemsNum<=5)) then 
         {
              fputs("[!(WItemsNum<=5)]#",fp_executionPath) and skip;
             if(!main_rand_x) then 
             {
                  fputs("[!rand_x]#",fp_executionPath) and skip;
                 break$<==1 and skip
                  
             }
             else 
             {
                  fputs("[!(!rand_x)]#",fp_executionPath) and skip
             }
             
         }
         else 
         {
              fputs("[!(!(WItemsNum<=5))]#",fp_executionPath) and skip 
         };
         if(break$=0)   then 
         {
             if(WItemsNum<=5) then 
             {
                  fputs("[WItemsNum<=5]#",fp_executionPath) and skip;
                 callback1();
                 WItemsNum:=WItemsNum+1
                 
             }
             else
             { 
              fputs("[!(WItemsNum<=5)]#",fp_executionPath) and skip;
             WItemsNum:=WItemsNum+1
         };
        
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_rand_x) and skip
	      }
	      else{
	         main_rand_x:=rand(RValue)
	      }
     }
     else
     {
         skip
     };

 break$<==0 and skip;
 fputs("[!(1)]#",fp_executionPath) and skip ;
 while(WItemsNum>2)
 {
      fputs("[WItemsNum>2]#",fp_executionPath) and skip;
     callback2();
     WItemsNum:=WItemsNum-1
 };
 fputs("[!(WItemsNum>2)]#",fp_executionPath) and skip
 )
 };
  main();
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
