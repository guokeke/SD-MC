frame(c,servers,resp,curr_serv,serversdiv2, s, fp_values, fp_executionPath) and (
FILE* fp_executionPath <== fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int c and skip;
int servers and skip;
int s and skip;
int resp and skip;
int curr_serv and skip;
int serversdiv2 and skip;
 function main ( int  RValue )
 {
     frame(main_rand_x,main_3_rand_x1,main_6_ddd) and (
     c:=rand();
     servers:=rand();
     s:=servers/2;
     serversdiv2:=rand();
     int main_rand_x and skip;
     main_rand_x:=rand();
     if(main_rand_x) then 
     {
        fputs("[main_rand_x]#" ,fp_executionPath ) and skip; 
        skip
         
     }
     else
     {
         fputs("![main_rand_x]#" ,fp_executionPath ) and skip; 
         skip
     };
     resp:=0;
     curr_serv:=servers;
     while(curr_serv>0)
     {
         fputs("[curr_serv>0]#" ,fp_executionPath ) and skip; 
         int main_3_rand_x1 and skip;
         main_3_rand_x1:=rand();
         if(main_3_rand_x1) then 
         {
             fputs("[main_3_rand_x1]#" ,fp_executionPath ) and skip; 
             c:=c-1;
             curr_serv:=curr_serv-1;
             resp:=resp+1
         }
         else
         {
             fputs("![main_3_rand_x1]#" ,fp_executionPath ) and skip; 
             curr_serv:=curr_serv-1
         }
     };
     fputs("![curr_serv>0]#" ,fp_executionPath ) and skip; 
     while(1)
     {
         fputs("[1]#" ,fp_executionPath ) and skip; 
         int main_6_ddd<==0 and skip;
         main_6_ddd:=main_6_ddd
     };
     fputs("![1]#" ,fp_executionPath ) and skip
     )
 };
  main(RValue)
 )
