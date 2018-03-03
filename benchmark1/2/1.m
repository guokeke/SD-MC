frame(pc,i,Pdolen,num,DName,lptNamei,dcIdi,Pdoi,PdoType,status,set,unset,fp_executionPath, fp_values) and (
FILE* fp_executionPath <== fopen("executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("values.txt", "r") and skip;
int pc and skip;
int i and skip;
int Pdolen and skip;
int num and skip;
int DName and skip;
int lptNamei and skip;
int dcIdi and skip;
int Pdoi and skip;
int PdoType and skip;
int status and skip;
int set<==0 and skip;
int unset<==0 and skip;
 function PPMakeDeviceName ( int a,int b,int c,int d,int RValue )
 {
     frame(PPMakeDeviceName_rand_x,return) and ( 
     int return<==0 and skip;
     int PPMakeDeviceName_rand_x and skip;
     //PPMakeDeviceName_rand_x:=rand(RValue);
	 fscanf(fp_values, "%d", &PPMakeDeviceName_rand_x) and skip;

     return<==1 and RValue:=PPMakeDeviceName_rand_x;
     skip
     )
     }; 
  function IoCreateDevice ( int a,int RValue )
 {
     frame(IoCreateDevice_rand_x,return) and ( 
     int return<==0 and skip;
     int IoCreateDevice_rand_x and skip;
     //IoCreateDevice_rand_x:=rand(RValue);
	  fscanf(fp_values, "%d", &IoCreateDevice_rand_x) and skip;

     return<==1 and RValue:=IoCreateDevice_rand_x;
     skip
     )
     }; 
  function ExFreePool ( int a )
 {
     skip
 };
 function PPBlockInits (  )
 {
     skip
 };
 function PPUnblockInits (  )
 {
     skip
 };
 function RtlInitUnicodeString ( int a )
 {
     skip
 };
 function main (  )
 {
     frame(goto,break$) and (
     int break$<==0 and skip;
     int goto<==0 and skip;
     set:=1;
     set:=0;
     PPBlockInits();
     break$<==0 and skip;
     while( break$=0 AND   i<Pdolen)
     {
          fputs("[i<Pdolen]\n" ,fp_executionPath ) and skip;
         DName:=PPMakeDeviceName(lptNamei,PdoType,dcIdi,num,RValue);
         if(!DName) then 
         {
              fputs("[!DName]\n",fp_executionPath) and skip;
             break$<==1 and skip
              
         }
         else 
         {
              fputs("[!(!DName)]\n",fp_executionPath) and skip 
         };
         if(break$=0)   then
         {
             RtlInitUnicodeString(DName);
             status:=IoCreateDevice(Pdoi,RValue);
             pc:=1;
             pc:=0;
             if(1!=status) then 
             {
                  fputs("[1!=status]\n",fp_executionPath) and skip;
                 Pdoi:=0;
                 if(2=status) then 
                 {
                      fputs("[2==status]\n",fp_executionPath) and skip;
                     ExFreePool(DName);
                     num:=num+1;
                     goto<==1 and skip
                     
                 }
                 else 
                 {
                      fputs("[!(2==status)]\n",fp_executionPath) and skip 
                 };
                 if(goto=0)   then 
                 {
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
         }
         else
         {
              fputs("[!(1!=status)]\n",fp_executionPath) and skip;
             i:=i+1
         }
     };
     break$<==0 and skip;
     fputs("[!(i<Pdolen)]\n",fp_executionPath) and skip ;
     if(goto=0)   then 
     {
         num:=0;
         unset:=1;
         unset:=0;
         PPUnblockInits()
     }
     else
     {
         skip
     }
     )
 };
  main()
 )
