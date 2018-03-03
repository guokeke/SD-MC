frame(fp_executionPath,fp_values,family,hostName,portNumber,unixSocketName,MaxListen,fd,err,maxconn,one,ret,service,hint,listen_index,added,addr_ai_family,addr,MAXADDR,ListenSocket_OF_listen_index,sock_path,addrs,rnode,istemp,firstDelBlock,A,RELEASE,bufHdr,bufHdr_tag_blockNum,bufHdr_tag_rnode,bufHdr_tag_rnode_spcNode,bufHdr_tag_rnode_dbNode,bufHdr_tag_rnode_relNode,bufHdr_flags,bufHdr_cntxDirty,LocalRefCount_i,LocalBufferDescriptors_i,NLocBuffer,i,NBuffers,bufHdr_refcount) and (
FILE* fp_executionPath <==fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;
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
int rnode and skip;
int istemp and skip;
int firstDelBlock and skip;
int A and skip;
int RELEASE and skip;
char *bufHdr and skip;
int bufHdr_tag_blockNum and skip;
int bufHdr_tag_rnode and skip;
int bufHdr_tag_rnode_spcNode and skip;
int bufHdr_tag_rnode_dbNode and skip;
int bufHdr_tag_rnode_relNode and skip;
int bufHdr_flags and skip;
int bufHdr_cntxDirty and skip;
int LocalRefCount_i and skip;
int LocalBufferDescriptors_i and skip;
int NLocBuffer and skip;
int i and skip;
int NBuffers and skip;
int bufHdr_refcount and skip;
 function StrategyInvalidateBuffer ( int bufHdr )
 {
     skip
 };
 function WaitIO ( int a )
 {
     skip
 };
 function RelFileNodeEquals ( int a,int b,int RValue )
 {
     frame(RelFileNodeEquals_rand_x,return) and ( 
     int return<==0 and skip;
     int RelFileNodeEquals_rand_x and skip;
	 if(!feof(fp_values))then{
         fscanf(fp_values, "%d", &RelFileNodeEquals_rand_x) and skip
	 }
	 else{
	     RelFileNodeEquals_rand_x:=rand(RValue)
	 };
     return<==1 and RValue:=RelFileNodeEquals_rand_x;
     skip
     )
     }; 
  function main (  )
 {
     frame(main_1_2_temp1,main_6_rand_x,main_6_temp2,goto) and (
     int goto<==0 and skip;
    

	 if(!feof(fp_values))then{
         fscanf(fp_values, "%d", &istemp) and skip
	 }
	 else{
	     istemp:=rand(RValue)
	 };

     A:=0;
     RELEASE:=0;
     

	 if(!feof(fp_values))then{
         fscanf(fp_values, "%d", &NLocBuffer) and skip
	 }
	 else{
	     NLocBuffer:=rand(RValue)
	 };

    

	 if(!feof(fp_values))then{
         fscanf(fp_values, "%d", &NBuffers) and skip
	 }
	 else{
	     NBuffers:=rand(RValue)
	 };


     if(istemp=1) then 
     {
          fputs("[istemp==1]#",fp_executionPath) and skip;
         i:=0;
         while( i<NLocBuffer)
         {
              fputs("[i<NLocBuffer]#" ,fp_executionPath ) and skip;
             bufHdr:=(char *)&LocalBufferDescriptors_i;
             int main_1_2_temp1 and skip;
             main_1_2_temp1:=RelFileNodeEquals(bufHdr_tag_rnode,rnode,RValue);
             if(main_1_2_temp1) then 
             {
                  fputs("[temp1]#",fp_executionPath) and skip;
                 if(bufHdr_tag_blockNum>=firstDelBlock) then 
                 {
                      fputs("[bufHdr_tag_blockNum>=firstDelBlock]#",fp_executionPath) and skip;
                     if(LocalRefCount_i!=0) then 
                     {
                          fputs("[LocalRefCount_i!=0]#",fp_executionPath) and skip;
                         skip
                         
                     }
                     else 
                     {
                          fputs("[!(LocalRefCount_i!=0)]#",fp_executionPath) and skip 
                     };
                     bufHdr_flags:=0;
                     bufHdr_cntxDirty:=0;
                     bufHdr_tag_rnode_relNode:=1
                     
                 }
                 else 
                 {
                      fputs("[!(bufHdr_tag_blockNum>=firstDelBlock)]#",fp_executionPath) and skip
                 }
                 
             }
             else 
             {
                  fputs("[!(temp1)]#",fp_executionPath) and skip 
             };
             i:=i+1
         };
         fputs("[!(i<NLocBuffer)]#",fp_executionPath) and skip ;
         goto<==1 and skip
         
     }
     else 
     {
          fputs("[!(istemp==1)]#",fp_executionPath) and skip 
     };
     if(goto=0)   then 
     {
         A:=1;
         A:=0;
         i:=1;
         while( i<=NBuffers)
         {
              fputs("[i<=NBuffers]#" ,fp_executionPath ) and skip;
             int main_6_rand_x and skip;


			  if(!feof(fp_values))then{
                 fscanf(fp_values, "%d", &main_6_rand_x) and skip
	          }
	          else{
	             main_6_rand_x:=rand(RValue)
	          };

             bufHdr:=(char *)main_6_rand_x;
             goto<==0 and skip;
             int main_6_temp2 and skip;
             main_6_temp2:=RelFileNodeEquals(bufHdr_tag_rnode,rnode,RValue);
             if(bufHdr_tag_blockNum>=firstDelBlock) then 
             {
                  fputs("[bufHdr_tag_blockNum>=firstDelBlock]#",fp_executionPath) and skip;
                 if(bufHdr_tag_blockNum>=firstDelBlock) then 
                 {
                      fputs("[bufHdr_tag_blockNum>=firstDelBlock]#",fp_executionPath) and skip;
                     if(bufHdr_flags) then 
                     {
                          fputs("[bufHdr_flags]#",fp_executionPath) and skip;
                         WaitIO((int)bufHdr);
                         goto<==1 and skip
                         
                     }
                     else 
                     {
                          fputs("[!(bufHdr_flags)]#",fp_executionPath) and skip 
                     };
                     if(goto=0)   then 
                     {
                         if(bufHdr_refcount!=0) then 
                         {
                              fputs("[bufHdr_refcount!=0]#",fp_executionPath) and skip;
                             skip
                             
                         }
                         else 
                         {
                              fputs("[!(bufHdr_refcount!=0)]#",fp_executionPath) and skip 
                         };
                         bufHdr_flags:=0;
                         bufHdr_cntxDirty:=0;
                         StrategyInvalidateBuffer((int)bufHdr)
                     }
                     else
                     {
                         skip
                     }
                     
                 }
                 else 
                 {
                      fputs("[!(bufHdr_tag_blockNum>=firstDelBlock)]#",fp_executionPath) and skip
                 }
                 
             }
             else 
             {
                  fputs("[!(bufHdr_tag_blockNum>=firstDelBlock)]#",fp_executionPath) and skip 
             };
             if(goto=0)   then 
             {
                 i:=i+1
             }
             else
             {
                 skip
             }
         };
         fputs("[!(i<=NBuffers)]#",fp_executionPath) and skip ;
         RELEASE:=1;
         RELEASE:=0;
         goto<==0 and skip;
         0 
     }
     else
     {
         skip
     }
     )
 };
  main();
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
