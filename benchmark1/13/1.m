frame(fp_executionPath,fp_values,a,r,irql,csl,status,OldIrql,CurrentTimeouts,lock,k,ListElement,Irp,IrpSp,CancelIrql,BytesToMove,FirstHalf,SecondHalf,LockHeld) and (
FILE* fp_executionPath <==fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;
int a and skip;
int r and skip;
int irql and skip;
int csl and skip;
int status and skip;
int OldIrql and skip;
int CurrentTimeouts and skip;
int lock and skip;
int k and skip;
int ListElement and skip;
int Irp and skip;
int IrpSp and skip;
int CancelIrql and skip;
int BytesToMove and skip;
int FirstHalf and skip;
int SecondHalf and skip;
int LockHeld and skip;
 function KeAcquireSpinLock ( int *lp,int *ip )
 {
     * lp:=1;
     * ip:=irql
     
 };
 function KeReleaseSpinLock ( int *lp,int i )
 {
     * lp:=0;
     irql:=i
     
 };
 function IoAcquireCancelSpinLock ( int *ip )
 {
     csl:=1;
     * ip:=irql
     
 };
 function IoReleaseCancelSpinLock ( int ip )
 {
     csl:=0;
     irql:=ip
     
 };
 function IoGetCurrentIrpStackLocation ( int a,int RValue )
 {
     frame(IoGetCurrentIrpStackLocation_rand_x,return) and ( 
     int return<==0 and skip;
     int IoGetCurrentIrpStackLocation_rand_x and skip;
     //IoGetCurrentIrpStackLocation_rand_x:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &IoGetCurrentIrpStackLocation_rand_x) and skip
	 }
	 else{
	    IoGetCurrentIrpStackLocation_rand_x:=rand(RValue)
	 };


     return<==1 and RValue:=IoGetCurrentIrpStackLocation_rand_x;
     skip
     )
     }; 
  function RemoveReferenceAndCompleteRequest ( int a,int b )
 {
     skip
 };
 function main (  )
 {
     frame(main_rand_x,main_rand_x1,main_rand_x2,main_1_rand_x3,main_1_rand_x4,main_1_rand_x5,main_1_9_10_rand_x6,main_1_13_rand_x7,main_1_13_14_rand_x8,main_1_13_14_16_rand_x8,break$,continue) and (
     int continue<==0 and skip;
     int break$<==0 and skip;
     status:=1;
     //CurrentTimeouts:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &CurrentTimeouts) and skip
	 }
	 else{
	    CurrentTimeouts:=rand(RValue)
	 };


     //k:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &k) and skip
	 }
	 else{
	    k:=rand(RValue)
	 };



     a:=1;
     a:=0;
     int main_rand_x and skip;
     //main_rand_x:=rand(RValue);
	  if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_rand_x) and skip
	 }
	 else{
	    main_rand_x:=rand(RValue)
	 };


     int main_rand_x1 and skip;
     //main_rand_x1:=rand(RValue);
	  if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_rand_x1) and skip
	 }
	 else{
	    main_rand_x1:=rand(RValue)
	 };

     int main_rand_x2 and skip;
     //main_rand_x2:=rand(RValue);
	 if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_rand_x2) and skip
	 }
	 else{
	    main_rand_x2:=rand(RValue)
	 };

     break$<==0 and skip;
     while( break$=0 AND   1)
     {
          fputs("[1]#" ,fp_executionPath ) and skip;
         continue<==0 and skip;
         if(main_rand_x!=0) then 
         {
              fputs("[rand_x!=0]#",fp_executionPath) and skip;
             if(k>0) then 
             {
                  fputs("[k>0]#",fp_executionPath) and skip;
                 if(!main_rand_x1) then 
                 {
                      fputs("[!rand_x1]#",fp_executionPath) and skip;
                     if(!main_rand_x2) then 
                     {
                          fputs("[!rand_x2]#",fp_executionPath) and skip;
                         break$<==1 and skip
                          
                     }
                     else 
                     {
                          fputs("[!(!rand_x2)]#",fp_executionPath) and skip
                     }
                     
                 }
                 else 
                 {
                      fputs("[!(!rand_x1)]#",fp_executionPath) and skip
                 }
             }
             else
             {
                  fputs("[!(k>0)]#",fp_executionPath) and skip;
                 break$<==1 and skip
              }
             
         }
         else
         { 
          fputs("[!(rand_x!=0)]#",fp_executionPath) and skip;
         break$<==1 and skip
      };
     if(break$=0)  then 
     {
         if(break$=0)   then 
         {
             //ListElement:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &ListElement) and skip
	 }
	 else{
	    ListElement:=rand(RValue)
	 };

             //Irp:=rand(RValue);
    if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &Irp) and skip
	 }
	 else{
	    Irp:=rand(RValue)
	 };


             //IrpSp:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &IrpSp) and skip
	 }
	 else{
	    IrpSp:=rand(RValue)
	 };


            // CancelIrql:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &CancelIrql) and skip
	 }
	 else{
	    CancelIrql:=rand(RValue)
	 };

             k:=k-1;
             //Irp:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &Irp) and skip
	 }
	 else{
	    Irp:=rand(RValue)
	 };


             IoAcquireCancelSpinLock(&CancelIrql);
             int main_1_rand_x3 and skip;
             //main_1_rand_x3:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_rand_x3) and skip
	 }
	 else{
	    main_1_rand_x3:=rand(RValue)
	 };


             if(main_1_rand_x3!=0) then 
             {
                  fputs("[rand_x3!=0]#",fp_executionPath) and skip;
                 IoReleaseCancelSpinLock(CancelIrql);
                 continue<==1 and skip
                  
             }
             else 
             {
                  fputs("[!(rand_x3!=0)]#",fp_executionPath) and skip 
             };
             if(continue=0)   then 
             {
                 IoReleaseCancelSpinLock(CancelIrql);
                 r:=1;
                 r:=0;
                 status:=1;
                 Irp:=NULL;
                 LockHeld:=1;
                 a:=1;
                 a:=0;
                 int main_1_rand_x4 and skip;
                 //main_1_rand_x4:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_rand_x4) and skip
	 }
	 else{
	    main_1_rand_x4:=rand(RValue)
	 };


                 int main_1_rand_x5 and skip;
                 //main_1_rand_x5:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_rand_x5) and skip
	 }
	 else{
	    main_1_rand_x5:=rand(RValue)
	 };


                 if(main_1_rand_x4!=0) then 
                 {
                      fputs("[rand_x4!=0]#",fp_executionPath) and skip;
                     if(main_1_rand_x5!=0) then 
                     {
                          fputs("[rand_x5]#",fp_executionPath) and skip;
                         //Irp:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &Irp) and skip
	 }
	 else{
	    Irp:=rand(RValue)
	 };


                         IrpSp:=IoGetCurrentIrpStackLocation(Irp,RValue);
                         //BytesToMove:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &BytesToMove) and skip
	 }
	 else{
	    BytesToMove:=rand(RValue)
	 };

                         int main_1_9_10_rand_x6 and skip;
                         //main_1_9_10_rand_x6:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_9_10_rand_x6) and skip
	 }
	 else{
	    main_1_9_10_rand_x6:=rand(RValue)
	 };

                         if(main_1_9_10_rand_x6!=0) then 
                         {
                              fputs("[rand_x6!=0]#",fp_executionPath) and skip;
                             //FirstHalf:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &FirstHalf) and skip
	 }
	 else{
	    FirstHalf:=rand(RValue)
	 };



                             SecondHalf:=BytesToMove-FirstHalf
                         }
                         else
                         {
                              fputs("[!(rand_x6!=0)]#",fp_executionPath) and skip;
                             skip
                         }
                         
                     }
                     else 
                     {
                          fputs("[!(rand_x5!=0)]#",fp_executionPath) and skip
                     }
                     
                 }
                 else
                 { 
                  fputs("[!(rand_x4!=0)]#",fp_executionPath) and skip;
                 int main_1_13_rand_x7 and skip;
                 //main_1_13_rand_x7:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_13_rand_x7) and skip
	 }
	 else{
	    main_1_13_rand_x7:=rand(RValue)
	 };


                 if(main_1_13_rand_x7!=0) then 
                 {
                      fputs("[rand_x7!=0]#",fp_executionPath) and skip;
                     //Irp:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &Irp) and skip
	 }
	 else{
	    Irp:=rand(RValue)
	 };


                     IoAcquireCancelSpinLock(&CancelIrql);
                     int main_1_13_14_rand_x8 and skip;
                     //main_1_13_14_rand_x8:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_13_14_rand_x8) and skip
	 }
	 else{
	    main_1_13_14_rand_x8:=rand(RValue)
	 };

                     if(main_1_13_14_rand_x8) then 
                     {
                          fputs("[rand_x8]#",fp_executionPath) and skip;
                         IoReleaseCancelSpinLock(CancelIrql);
                         r:=1;
                         r:=0;
                         RemoveReferenceAndCompleteRequest(Irp,2);
                         LockHeld:=0
                         
                     }
                     else
                     { 
                      fputs("[!(rand_x8)]#",fp_executionPath) and skip;
                     //CurrentTimeouts:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &CurrentTimeouts) and skip
	 }
	 else{
	    CurrentTimeouts:=rand(RValue)
	 };

                     int main_1_13_14_16_rand_x8 and skip;
                     //main_1_13_14_16_rand_x8:=rand(RValue);
	if(!feof(fp_values)) then{
	    fscanf(fp_values, "%d", &main_1_13_14_16_rand_x8) and skip
	 }
	 else{
	    main_1_13_14_16_rand_x8:=rand(RValue)
	 };


                     if(main_1_13_14_16_rand_x8!=0) then 
                     {
                          fputs("[rand_x8!=0]#",fp_executionPath) and skip;
                         IoReleaseCancelSpinLock(CancelIrql);
                         r:=1;
                         r:=0;
                         RemoveReferenceAndCompleteRequest(Irp,3);
                         LockHeld:=0
                     }
                     else
                     {
                          fputs("[!(rand_x8!=0)]#",fp_executionPath) and skip;
                         IoReleaseCancelSpinLock(CancelIrql);
                         k:=k-1
                     }
                 };
                 Irp:=NULL
                 
             }
             else 
             {
                  fputs("[!(rand_x7!=0)]#",fp_executionPath) and skip
             }
         };
         if(LockHeld=1) then 
         {
              fputs("[LockHeld==1]#",fp_executionPath) and skip;
             r:=1;
             r:=0
             
         }
         else 
         {
              fputs("[!(LockHeld==1)]#",fp_executionPath) and skip 
         };
         if(Irp!=0) then 
         {
              fputs("[Irp!=0]#",fp_executionPath) and skip;
             RemoveReferenceAndCompleteRequest(Irp,1)
             
         }
         else 
         {
              fputs("[!(Irp!=0)]#",fp_executionPath) and skip 
         };
         a:=1;
         a:=0
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
 fputs("[!(1)]#",fp_executionPath) and skip ;
 r:=1;
 r:=0
 )
 };
  main();
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
