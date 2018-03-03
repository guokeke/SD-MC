frame(i,c,fp_values,servers,resp,curr_serv, fp_executionPath, file) and (
FILE* fp_executionPath <== fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int c and skip;
int servers and skip;
int resp and skip;
int curr_serv and skip;
 function main ( int RValue )
 {
     frame(main_1_rand_x,main_4_ddd) and (
     //c:=random(RValue);
	 scanf(fp_values, "%d", &c) and skip;
     servers:=4;
     resp:=0;
     curr_serv:=servers;
     while( curr_serv>0)
     {
          
		 fputs("[curr_serv>0]#" ,fp_executionPath ) and skip;
         int main_1_rand_x and skip;
         //main_1_rand_x:=random(RValue);
		 scanf(fp_values, "%d", &main_1__rand_x) and skip;
		 
         if(main_1_rand_x) then 
         {
              fputs("[rand_x]#",fp_executionPath) and skip;
             c:=c-1;
             curr_serv:=curr_serv-1;
             resp:=resp+1
         }
         else
         {
              fputs("[!(rand_x)]#",fp_executionPath) and skip;
             curr_serv:=curr_serv-1
         }
     };
     fputs("[!(curr_serv>0)]#",fp_executionPath) and skip ;
	 int i<==0 and skip;
     while(i<10)
     {
          fputs("[i<10]#",fp_executionPath) and skip;
         int main_4_ddd and skip;
         main_4_ddd:=main_4_ddd;
		 i:=i+1
     };
     fputs("[!(i<10)]#",fp_executionPath) and skip
     )
 };
  main(RValue)
 )
