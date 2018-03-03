frame(x, fp_executionPath, fp_values) and (
FILE* fp_executionPath <== fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int x and skip;
 function main (  )
 {
     frame(main_rand_x) and (
     x:=1;
     int main_rand_x and skip;
     //main_rand_x:=rand(RValue);

	 fscanf(fp_values, "%d", &main_rand_x) and skip;
     while( main_rand_x)
     {
          fputs("[rand_x]\n" ,fp_executionPath ) and skip;
         //main_rand_x:=rand(RValue)
		  fscanf(fp_values, "%d", &main_rand_x) and skip
     };
     fputs("[!(rand_x)]\n",fp_executionPath) and skip ;
     x:=0;
     x:=1
    /* while(1)
     {
          fputs("[1]\n",fp_executionPath) and skip
     };
     fputs("[!(1)]\n",fp_executionPath) and skip*/
     )
 };
  main()
 )
