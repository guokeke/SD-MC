frame(fp_executionPath,fp_values,lock,CancelIrql,irql,csl,CurrentWaitIrp,NewMask,CancelIrp,Mask,length,NewTimeouts,SerialStatus,pBaudRate,pLineControl,LData,LStop,LParity,keA,keR,DeviceObject,Irp,status,OldIrql) and (
FILE* fp_executionPath <==fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
FILE * fp_values <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r") and skip;
int lock and skip;
int CancelIrql and skip;
int irql and skip;
int csl and skip;
int CurrentWaitIrp<==0 and skip;
int NewMask and skip;
int CancelIrp and skip;
int Mask and skip;
int length and skip;
int NewTimeouts and skip;
int SerialStatus and skip;
int pBaudRate and skip;
int pLineControl and skip;
int LData and skip;
int LStop and skip;
int LParity and skip;
int keA and skip;
int keR and skip;
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
 function IoMarkIrpPending ( int x )
 {
     skip
 };
 function RemoveReferenceAndCompleteRequest ( int x,int y )
 {
     skip
 };
 function RemoveReferenceForDispatch ( int x )
 {
     skip
 };
 function ProcessConnectionStateChange ( int x )
 {
     skip
 };
 int DeviceObject and skip;
 int Irp and skip;
 int status and skip;
 int OldIrql and skip;
 function main ( int RValue )
 {
     frame(main_1_2_ddd2,main_3_rand_x,main_3_rand_x2,main_3_rand_x4,main_3_rand_x7,main_3_rand_x11,main_3_rand_x13,main_3_rand_x16,main_3_rand_x18,main_3_rand_x20,main_3_rand_x23,main_3_rand_x25,main_3_rand_x27,main_3_rand_x29,main_3_rand_x30,main_3_rand_x31,main_3_4_rand_x1,main_3_6_7_rand_x3,main_3_6_11_12_rand_x5,main_3_6_11_12_rand_x6,main_3_6_11_17_18_rand_x8,main_3_6_11_17_18_20_21_rand_x9,main_3_6_11_17_18_20_rand_x10,main_3_6_11_17_25_26_rand_x12,main_3_6_11_17_25_28_29_rand_x14,main_3_6_11_17_25_28_29_rand_x15,main_3_6_11_17_25_28_32_33_rand_x17,main_3_6_11_17_25_28_32_35_36_rand_x19,main_3_6_11_17_25_28_32_35_38_39_rand_x21,main_3_6_11_17_25_28_32_35_38_39_41_rand_x22,main_3_6_11_17_25_28_32_35_38_43_44_rand_x24,main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26,main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42,main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x43,main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32,continue) and (
     int continue<==0 and skip;
     keA:=0;
     keR:=0;
     lock:=0;
     //CancelIrql:=rand(RValue);
	 if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &CancelIrql) and skip
	 }
	 else{
	     CancelIrql:=rand(RValue)
	 };


     //irql:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &irql) and skip
	 }
	 else{
	     irql:=rand(RValue)
	 };


     //csl:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &csl) and skip
	 }
	 else{
	     csl:=rand(RValue)
	 };

     //DeviceObject:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &DeviceObject) and skip
	 }
	 else{
	     DeviceObject:=rand(RValue)
	 };

     //Irp:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &Irp) and skip
	 }
	 else{
	     Irp:=rand(RValue)
	 };


     status:=1;
     OldIrql and skip;
     //status:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &status) and skip
	 }
	 else{
	     status:=rand(RValue)
	 };

     keA:=0;
     keR:=0;
     //length:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &length) and skip
	 }
	 else{
	     length:=rand(RValue)
	 };

     //NewTimeouts:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &NewTimeouts) and skip
	 }
	 else{
	     NewTimeouts:=rand(RValue)
	 };

     //SerialStatus:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &SerialStatus) and skip
	 }
	 else{
	     SerialStatus:=rand(RValue)
	 };

     //pBaudRate:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &pBaudRate) and skip
	 }
	 else{
	     pBaudRate:=rand(RValue)
	 };

     //pLineControl:=rand(RValue);
	  if(!feof(fp_values))then{
	    fscanf(fp_values, "%d", &pLineControl) and skip
	 }
	 else{
	     pLineControl:=rand(RValue)
	 };

     LData:=0;
     LStop:=0;
     LParity:=0;
     Mask:=255;
     if(2!=status) then 
     {
          fputs("[2!=status]#",fp_executionPath) and skip;
         while(1)
         {
              fputs("[1]#",fp_executionPath) and skip;
             int main_1_2_ddd2<==0 and skip;
             main_1_2_ddd2:=main_1_2_ddd2
         };
         fputs("[!(1)]#",fp_executionPath) and skip
         
     }
     else 
     {
          fputs("[!(2!=status)]#",fp_executionPath) and skip 
     };
     if(1) then 
     {
          fputs("[1]#",fp_executionPath) and skip;
         int main_3_rand_x and skip;
         //main_3_rand_x:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x) and skip
	      }
	      else{
	         main_3_rand_x:=rand(RValue)
	      };

         int main_3_rand_x2 and skip;
         //main_3_rand_x2:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x2) and skip
	      }
	      else{
	         main_3_rand_x2:=rand(RValue)
	      };


         int main_3_rand_x4 and skip;
         //main_3_rand_x4:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x4) and skip
	      }
	      else{
	         main_3_rand_x4:=rand(RValue)
	      };


         int main_3_rand_x7 and skip;
         //main_3_rand_x7:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x7) and skip
	      }
	      else{
	         main_3_rand_x7:=rand(RValue)
	      };

         int main_3_rand_x11 and skip;
         //main_3_rand_x11:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x11) and skip
	      }
	      else{
	         main_3_rand_x11:=rand(RValue)
	      };

         int main_3_rand_x13 and skip;
        // main_3_rand_x13:=rand(RValue);
		 if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x13) and skip
	      }
	      else{
	         main_3_rand_x13:=rand(RValue)
	      };


         int main_3_rand_x16 and skip;
         //main_3_rand_x16:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x16) and skip
	      }
	      else{
	         main_3_rand_x16:=rand(RValue)
	      };

         int main_3_rand_x18 and skip;
         //main_3_rand_x18:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x18) and skip
	      }
	      else{
	         main_3_rand_x18:=rand(RValue)
	      };

         int main_3_rand_x20 and skip;
         //main_3_rand_x20:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x20) and skip
	      }
	      else{
	         main_3_rand_x20:=rand(RValue)
	      };

         int main_3_rand_x23 and skip;
         //main_3_rand_x23:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x23) and skip
	      }
	      else{
	         main_3_rand_x23:=rand(RValue)
	      };

         int main_3_rand_x25 and skip;
         //main_3_rand_x25:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x25) and skip
	      }
	      else{
	         main_3_rand_x25:=rand(RValue)
	      };


         int main_3_rand_x27 and skip;
         //main_3_rand_x27:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x27) and skip
	      }
	      else{
	         main_3_rand_x27:=rand(RValue)
	      };

         int main_3_rand_x29 and skip;
         //main_3_rand_x29:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x29) and skip
	      }
	      else{
	         main_3_rand_x29:=rand(RValue)
	      };

         int main_3_rand_x30 and skip;
         //main_3_rand_x30:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x30) and skip
	      }
	      else{
	         main_3_rand_x30:=rand(RValue)
	      };

         int main_3_rand_x31 and skip;
         //main_3_rand_x31:=rand(RValue);
		  if(!feof(fp_values))then{
	         fscanf(fp_values, "%d", &main_3_rand_x31) and skip
	      }
	      else{
	         main_3_rand_x31:=rand(RValue)
	      };

         if(main_3_rand_x!=0) then 
         {
              fputs("[rand_x!=0]#",fp_executionPath) and skip;
             int main_3_4_rand_x1 and skip;
             main_3_4_rand_x1:=rand(RValue);
			 if(!feof(fp_values))then{
	            fscanf(fp_values, "%d", &main_3_4_rand_x1) and skip
	         }
	         else{
	            main_3_4_rand_x1:=rand(RValue)
	         };


             if(main_3_4_rand_x1!=0) then 
             {
                  fputs("[rand_x1!=0]#",fp_executionPath) and skip;
                 status:=4
                 
             }
             else 
             {
                  fputs("[!(rand_x1!=0)]#",fp_executionPath) and skip
             }
         }
         else
         {
              fputs("[!(rand_x!=0)]#",fp_executionPath) and skip;
             if(main_3_rand_x2!=0) then 
             {
                  fputs("[rand_x2!=0]#",fp_executionPath) and skip;
                 CurrentWaitIrp:=0;
                 //NewMask:=rand(RValue);
				  if(!feof(fp_values))then{
	                fscanf(fp_values, "%d", &NewMask) and skip
	              }
	              else{
	                NewMask:=rand(RValue)
	              };


                 int main_3_6_7_rand_x3 and skip;
                 //main_3_6_7_rand_x3:=rand(RValue);
				  if(!feof(fp_values))then{
	                fscanf(fp_values, "%d", &main_3_6_7_rand_x3) and skip
	              }
	              else{
	                main_3_6_7_rand_x3:=rand(RValue)
	              };

                 if(main_3_6_7_rand_x3!=0) then 
                 {
                      fputs("[rand_x3!=0]#",fp_executionPath) and skip;
                     status:=4
                 }
                 else
                 {
                      fputs("[!(rand_x3!=0)]#",fp_executionPath) and skip;
                     keA:=1;
                     keA:=0;
                     lock:=1;
                     OldIrql:=irql;
                     //NewMask:=rand(RValue);
					  if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &NewMask) and skip
	                   }
	                   else{
	                     NewMask:=rand(RValue)
	                   };


                     keR:=1;
                     keR:=0;
                     lock:=0;
                     irql:=OldIrql;
                     if(CurrentWaitIrp!=0) then 
                     {
                          fputs("[CurrentWaitIrp!=0]#",fp_executionPath) and skip;
                         RemoveReferenceAndCompleteRequest(CurrentWaitIrp,2)
                         
                     }
                     else 
                     {
                          fputs("[!(CurrentWaitIrp!=0)]#",fp_executionPath) and skip
                     }
                 }
             }
             else
             {
                  fputs("[!(rand_x2!=0)]#",fp_executionPath) and skip;
                 if(main_3_rand_x4!=0) then 
                 {
                      fputs("[rand_x4!=0]#",fp_executionPath) and skip;
                     CurrentWaitIrp:=0;
                     int main_3_6_11_12_rand_x5 and skip;
                     //main_3_6_11_12_rand_x5:=rand(RValue);
					   if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &main_3_6_11_12_rand_x5) and skip
	                   }
	                   else{
	                     main_3_6_11_12_rand_x5:=rand(RValue)
	                   };



                     if(main_3_6_11_12_rand_x5!=0) then 
                     {
                          fputs("[rand_x5!=0]#",fp_executionPath) and skip;
                         status:=4
                         
                     }
                     else 
                     {
                          fputs("[!(rand_x5!=0)]#",fp_executionPath) and skip 
                     };
                     keA:=1;
                     keA:=0;
                     lock:=1;
                     OldIrql:=irql;
                     //CurrentWaitIrp:=rand(RValue);
					  if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &CurrentWaitIrp) and skip
	                   }
	                   else{
	                     CurrentWaitIrp:=rand(RValue)
	                   };


                     int main_3_6_11_12_rand_x6 and skip;
                     //main_3_6_11_12_rand_x6:=rand(RValue);
					  if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &main_3_6_11_12_rand_x6) and skip
	                   }
	                   else{
	                     main_3_6_11_12_rand_x6:=rand(RValue)
	                   };


                     if(main_3_6_11_12_rand_x6!=0) then 
                     {
                          fputs("[rand_x6!=0]#",fp_executionPath) and skip;
                         status:=1
                         
                     }
                     else
                     { 
                      fputs("[!(rand_x6!=0)]#",fp_executionPath) and skip;
                     IoMarkIrpPending(Irp);
                     status:=7
                 };
                 keR:=1;
                 keR:=0;
                 lock:=0;
                 irql:=OldIrql;
                 if(CurrentWaitIrp!=0) then 
                 {
                      fputs("[CurrentWaitIrp!=0]#",fp_executionPath) and skip;
                     RemoveReferenceAndCompleteRequest(CurrentWaitIrp,2)
                     
                 }
                 else 
                 {
                      fputs("[!(CurrentWaitIrp!=0)]#",fp_executionPath) and skip
                 }
             }
             else
             {
                  fputs("[!(rand_x4!=0)]#",fp_executionPath) and skip;
                 if(main_3_rand_x7!=0) then 
                 {
                      fputs("[rand_x7!=0]#",fp_executionPath) and skip;
                     //CancelIrp:=rand(RValue);
					   if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &CancelIrp) and skip
	                   }
	                   else{
	                     CancelIrp:=rand(RValue)
	                   };


                     //Mask:=rand(RValue);
					  if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &Mask) and skip
	                   }
	                   else{
	                     Mask:=rand(RValue)
	                   };


                     int main_3_6_11_17_18_rand_x8 and skip;
                     //main_3_6_11_17_18_rand_x8:=rand(RValue);
					   if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &main_3_6_11_17_18_rand_x8) and skip
	                   }
	                   else{
	                     main_3_6_11_17_18_rand_x8:=rand(RValue)
	                   };


                     if(main_3_6_11_17_18_rand_x8!=0) then 
                     {
                          fputs("[rand_x8!=0]#",fp_executionPath) and skip;
                         status:=4
                         
                     }
                     else 
                     {
                          fputs("[!(rand_x8!=0)]#",fp_executionPath) and skip 
                     };
                     if(Mask!=0) then 
                     {
                          fputs("[Mask!=0]#",fp_executionPath) and skip;
                         keA:=1;
                         keA:=0;
                         lock:=1;
                         OldIrql:=irql;
                         //length:=rand(RValue);
						 if(!feof(fp_values))then{
	                     fscanf(fp_values, "%d", &length) and skip
	                   }
	                   else{
	                     length:=rand(RValue)
	                   };


                         while( length>0)
                         {
                              fputs("[length>0]#" ,fp_executionPath ) and skip;
                             continue<==0 and skip;
                             length:=length-1;
                             //CancelIrp:=rand(RValue);
							 if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &CancelIrp) and skip
	                         }
	                         else{
	                           CancelIrp:=rand(RValue)
	                         };


                             IoAcquireCancelSpinLock(&CancelIrql);
                             int main_3_6_11_17_18_20_21_rand_x9 and skip;
                             //main_3_6_11_17_18_20_21_rand_x9:=rand(RValue);
							  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_18_20_21_rand_x9) and skip
	                         }
	                         else{
	                           main_3_6_11_17_18_20_21_rand_x9:=rand(RValue)
	                         };



                             if(main_3_6_11_17_18_20_21_rand_x9!=0) then 
                             {
                                  fputs("[rand_x9!=0]#",fp_executionPath) and skip;
                                 IoReleaseCancelSpinLock(CancelIrql);
                                 continue<==1 and skip
                                  
                             }
                             else 
                             {
                                  fputs("[!(rand_x9!=0)]#",fp_executionPath) and skip 
                             };
                             if(continue=0)   then 
                             {
                                 IoReleaseCancelSpinLock(CancelIrql);
                                 keR:=1;
                                 keR:=0;
                                 lock:=0;
                                 irql:=OldIrql;
                                 RemoveReferenceAndCompleteRequest(CancelIrp,11);
                                 keA:=1;
                                 keA:=0;
                                 lock:=1;
                                 OldIrql:=irql
                             }
                             else
                             {
                                 skip
                             }
                         };
                         continue<==0 and skip;
                         fputs("[!(length>0)]#",fp_executionPath) and skip ;
                         CancelIrp:=NULL;
                         int main_3_6_11_17_18_20_rand_x10 and skip;
                         //main_3_6_11_17_18_20_rand_x10:=rand(RValue);
						   if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_18_20_rand_x10) and skip
	                         }
	                         else{
	                           main_3_6_11_17_18_20_rand_x10:=rand(RValue)
	                         };


                         if(main_3_6_11_17_18_20_rand_x10!=0) then 
                         {
                              fputs("[rand_x10!=0]#",fp_executionPath) and skip;
                             //CancelIrp:=rand(RValue);

							  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &CancelIrp) and skip
	                         }
	                         else{
	                           CancelIrp:=rand(RValue)
	                         }
                             
                         }
                         else 
                         {
                              fputs("[!(rand_x10!=0)]#",fp_executionPath) and skip 
                         };
                         keR:=1;
                         keR:=0;
                         lock:=0;
                         irql:=OldIrql;
                         if(CancelIrp!=NULL) then 
                         {
                              fputs("[CancelIrp!=NULL]#",fp_executionPath) and skip;
                             RemoveReferenceAndCompleteRequest(CancelIrp,11)
                             
                         }
                         else 
                         {
                              fputs("[!(CancelIrp!=NULL)]#",fp_executionPath) and skip
                         }
                         
                     }
                     else 
                     {
                          fputs("[!(Mask!=0)]#",fp_executionPath) and skip
                     }
                 }
                 else
                 {
                      fputs("[!(rand_x7!=0)]#",fp_executionPath) and skip;
                     if(main_3_rand_x11!=0) then 
                     {
                          fputs("[rand_x11!=0]#",fp_executionPath) and skip;
                         int main_3_6_11_17_25_26_rand_x12 and skip;
                         //main_3_6_11_17_25_26_rand_x12:=rand(RValue);
						 
							  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_25_26_rand_x12) and skip
	                         }
	                         else{
	                           main_3_6_11_17_25_26_rand_x12:=rand(RValue)
	                         };


                         if(main_3_6_11_17_25_26_rand_x12!=0) then 
                         {
                              fputs("[rand_x12!=0]#",fp_executionPath) and skip;
                             status:=4
                             
                         }
                         else 
                         {
                              fputs("[!(rand_x12!=0)]#",fp_executionPath) and skip
                         }
                     }
                     else
                     {
                          fputs("[!(rand_x11!=0)]#",fp_executionPath) and skip;
                         if(main_3_rand_x13!=0) then 
                         {
                              fputs("[rand_x13!=0]#",fp_executionPath) and skip;
                             //NewTimeouts:=rand(RValue);
							  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &NewTimeouts) and skip
	                         }
	                         else{
	                           NewTimeouts:=rand(RValue)
	                         };


                             int main_3_6_11_17_25_28_29_rand_x14 and skip;
                             //main_3_6_11_17_25_28_29_rand_x14:=rand(RValue);
							 if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_25_28_29_rand_x14) and skip
	                         }
	                         else{
	                           main_3_6_11_17_25_28_29_rand_x14:=rand(RValue)
	                         };


                             if(main_3_6_11_17_25_28_29_rand_x14!=0) then 
                             {
                                  fputs("[rand_x14!=0]#",fp_executionPath) and skip;
                                 status:=4
                                 
                             }
                             else 
                             {
                                  fputs("[!(rand_x14!=0)]#",fp_executionPath) and skip 
                             };
                             int main_3_6_11_17_25_28_29_rand_x15 and skip;
                             //main_3_6_11_17_25_28_29_rand_x15:=rand(RValue);
							  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_25_28_29_rand_x15) and skip
	                         }
	                         else{
	                           main_3_6_11_17_25_28_29_rand_x15:=rand(RValue)
	                         };


                             if(main_3_6_11_17_25_28_29_rand_x15!=0) then 
                             {
                                  fputs("[rand_x15!=0]#",fp_executionPath) and skip;
                                 status:=15
                                 
                             }
                             else 
                             {
                                  fputs("[!(rand_x15!=0)]#",fp_executionPath) and skip 
                             };
                             keA:=1;
                             keA:=0;
                             lock:=1;
                             OldIrql:=irql;
                             keR:=1;
                             keR:=0;
                             lock:=0;
                             irql:=OldIrql
                         }
                         else
                         {
                              fputs("[!(rand_x13!=0)]#",fp_executionPath) and skip;
                             if(main_3_rand_x16!=0) then 
                             {
                                  fputs("[rand_x16!=0]#",fp_executionPath) and skip;
                                 int main_3_6_11_17_25_28_32_33_rand_x17 and skip;
                                 //main_3_6_11_17_25_28_32_33_rand_x17:=rand(RValue);
								  if(!feof(fp_values))then{
										fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_33_rand_x17) and skip
								  }
								  else{
										main_3_6_11_17_25_28_32_33_rand_x17:=rand(RValue)
								  };


                                 if(main_3_6_11_17_25_28_32_33_rand_x17!=0) then 
                                 {
                                      fputs("[rand_x17!=0]#",fp_executionPath) and skip;
                                     status:=4
                                     
                                 }
                                 else 
                                 {
                                      fputs("[!(rand_x17!=0)]#",fp_executionPath) and skip 
                                 };
                                 keA:=1;
                                 keA:=0;
                                 lock:=1;
                                 OldIrql:=irql;
                                 keR:=1;
                                 keR:=0;
                                 lock:=0;
                                 irql:=OldIrql
                             }
                             else
                             {
                                  fputs("[!(rand_x16!=0)]#",fp_executionPath) and skip;
                                 if(main_3_rand_x18!=0) then 
                                 {
                                      fputs("[rand_x18!=0]#",fp_executionPath) and skip;
                                     //SerialStatus:=rand(RValue);
									   if(!feof(fp_values))then{
											fscanf(fp_values, "%d", &SerialStatus) and skip
										}
										else{
											SerialStatus:=rand(RValue)
										};


                                     int main_3_6_11_17_25_28_32_35_36_rand_x19 and skip;
                                     //main_3_6_11_17_25_28_32_35_36_rand_x19:=rand(RValue);
									 if(!feof(fp_values))then{
										fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_36_rand_x19) and skip
									 }
									 else{
										main_3_6_11_17_25_28_32_35_36_rand_x19:=rand(RValue)
									 };


                                     if(main_3_6_11_17_25_28_32_35_36_rand_x19!=0) then 
                                     {
                                          fputs("[rand_x19!=0]#",fp_executionPath) and skip;
                                         status:=4
                                         
                                     }
                                     else 
                                     {
                                          fputs("[!(rand_x19!=0)]#",fp_executionPath) and skip 
                                     };
                                     keA:=1;
                                     keA:=0;
                                     lock:=1;
                                     OldIrql:=irql;
                                     keR:=1;
                                     keR:=0;
                                     lock:=0;
                                     irql:=OldIrql
                                 }
                                 else
                                 {
                                      fputs("[!(rand_x18!=0)]#",fp_executionPath) and skip;
                                     if(main_3_rand_x20!=0) then 
                                     {
                                          fputs("[rand_x20!=0]#",fp_executionPath) and skip;
                                         keA:=1;
                                         keA:=0;
                                         lock:=1;
                                         OldIrql:=irql;
                                         int main_3_6_11_17_25_28_32_35_38_39_rand_x21 and skip;
                                        // main_3_6_11_17_25_28_32_35_38_39_rand_x21:=rand(RValue);
										 if(!feof(fp_values))then{
											fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_39_rand_x21) and skip
										 }
										 else{
											main_3_6_11_17_25_28_32_35_38_39_rand_x21:=rand(RValue)
										 };


                                         if(main_3_6_11_17_25_28_32_35_38_39_rand_x21!=0) then 
                                         {
                                              fputs("[rand_x21!=0]#",fp_executionPath) and skip;
                                             skip
                                             
                                         }
                                         else
                                         { 
                                          fputs("[!(rand_x21!=0)]#",fp_executionPath) and skip;
                                         int main_3_6_11_17_25_28_32_35_38_39_41_rand_x22 and skip;
                                         //main_3_6_11_17_25_28_32_35_38_39_41_rand_x22:=rand(RValue);
										  if(!feof(fp_values))then{
												fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_39_41_rand_x22) and skip
										   }
										  else{
	                                            main_3_6_11_17_25_28_32_35_38_39_41_rand_x22:=rand(RValue)
	                                       };


                                         if(main_3_6_11_17_25_28_32_35_38_39_41_rand_x22!=0) then 
                                         {
                                              fputs("[rand_x22!=0]#",fp_executionPath) and skip;
                                             skip
                                             
                                         }
                                         else 
                                         {
                                              fputs("[!(rand_x22!=0)]#",fp_executionPath) and skip
                                         }
                                     };
                                     keR:=1;
                                     keR:=0;
                                     lock:=0;
                                     irql:=OldIrql;
                                     ProcessConnectionStateChange(DeviceObject)
                                 }
                                 else
                                 {
                                      fputs("[!(rand_x20!=0)]#",fp_executionPath) and skip;
                                     if(main_3_rand_x23!=0) then 
                                     {
                                          fputs("[rand_x23!=0]#",fp_executionPath) and skip;
                                         int main_3_6_11_17_25_28_32_35_38_43_44_rand_x24 and skip;
                                         //main_3_6_11_17_25_28_32_35_38_43_44_rand_x24:=rand(RValue);
										 	  if(!feof(fp_values))then{
	                            fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_44_rand_x24) and skip
	                         }
	                         else{
	                           main_3_6_11_17_25_28_32_35_38_43_44_rand_x24:=rand(RValue)
	                         };


                                         if(main_3_6_11_17_25_28_32_35_38_43_44_rand_x24!=0) then 
                                         {
                                              fputs("[rand_x24!=0]#",fp_executionPath) and skip;
                                             status:=4
                                             
                                         }
                                         else 
                                         {
                                              fputs("[!(rand_x24!=0)]#",fp_executionPath) and skip
                                         }
                                     }
                                     else
                                     {
                                          fputs("[!(rand_x23!=0)]#",fp_executionPath) and skip;
                                         if(main_3_rand_x25!=0) then 
                                         {
                                              fputs("[rand_x25!=0]#",fp_executionPath) and skip;
                                             int main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26 and skip;
                                             //main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26:=rand(RValue);
											  if(!feof(fp_values))then{
												    fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26) and skip
												}
											else{
												    main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26:=rand(RValue)
												};


                                             if(main_3_6_11_17_25_28_32_35_38_43_46_47_rand_x26!=0) then 
                                             {
                                                  fputs("[rand_x26!=0]#",fp_executionPath) and skip;
                                                 status:=4
                                             }
                                             else
                                             {
                                                  fputs("[!(rand_x26!=0)]#",fp_executionPath) and skip;
                                                 keA:=1;
                                                 keA:=0;
                                                 lock:=1;
                                                 OldIrql:=irql;
                                                 keR:=1;
                                                 keR:=0;
                                                 lock:=0;
                                                 irql:=OldIrql
                                             }
                                         }
                                         else
                                         {
                                              fputs("[!(rand_x25!=0)]#",fp_executionPath) and skip;
                                             if(main_3_rand_x27!=0) then 
                                             {
                                                  fputs("[rand_x27!=0]#",fp_executionPath) and skip;
                                                 //pBaudRate:=rand(RValue);
												   if(!feof(fp_values))then{
														fscanf(fp_values, "%d", &pBaudRate) and skip
													}
												    else{
														pBaudRate:=rand(RValue)
													};

                                                 int main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28 and skip;
                                                 //main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28:=rand(RValue);
												   if(!feof(fp_values))then{
														fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28) and skip
													}
													else{
														main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28:=rand(RValue)
													};



                                                 if(main_3_6_11_17_25_28_32_35_38_43_46_50_51_rand_x28!=0) then 
                                                 {
                                                      fputs("[rand_x28!=0]#",fp_executionPath) and skip;
                                                     status:=4
                                                 }
                                                 else
                                                 {
                                                      fputs("[!(rand_x28!=0)]#",fp_executionPath) and skip;
                                                     keA:=1;
                                                     keA:=0;
                                                     lock:=1;
                                                     OldIrql:=irql;
                                                     keR:=1;
                                                     keR:=0;
                                                     lock:=0;
                                                     irql:=OldIrql
                                                 }
                                             }
                                             else
                                             {
                                                  fputs("[!(rand_x27!=0)]#",fp_executionPath) and skip;
                                                 if(main_3_rand_x29!=0) then 
                                                 {
                                                      fputs("[rand_x29!=0]#",fp_executionPath) and skip;
                                                     //pLineControl:=rand(RValue);
													   if(!feof(fp_values))then{
															fscanf(fp_values, "%d", &pLineControl) and skip
														}
														else{
															pLineControl:=rand(RValue)
														};

                                                     LData:=0;
                                                     LStop:=0;
                                                     LParity:=0;
                                                     Mask:=255;
                                                     int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30 and skip;
                                                     //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30:=rand(RValue);
													   if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30:=rand(RValue)
	                                                   };


                                                     if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_rand_x30!=0) then 
                                                     {
                                                          fputs("[rand_x30!=0]#",fp_executionPath) and skip;
                                                         status:=4
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(rand_x30!=0)]#",fp_executionPath) and skip 
                                                     };
                                                     if(1) then 
                                                     {
                                                          fputs("[1]#",fp_executionPath) and skip;
                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31:=rand(RValue);
														 if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31:=rand(RValue)
	                                                   };



                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33:=rand(RValue);
														 if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34:=rand(RValue)
	                                                   };

                                                         if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x31!=0) then 
                                                         {
                                                              fputs("[rand_x31!=0]#",fp_executionPath) and skip;
                                                             LData:=27;
                                                             Mask:=31
                                                         }
                                                         else
                                                         {
                                                              fputs("[!(rand_x31!=0)]#",fp_executionPath) and skip;
                                                             if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x32!=0) then 
                                                             {
                                                                  fputs("[rand_x32!=0]#",fp_executionPath) and skip;
                                                                 LData:=24;
                                                                 Mask:=63
                                                             }
                                                             else
                                                             {
                                                                  fputs("[!(rand_x32!=0)]#",fp_executionPath) and skip;
                                                                 if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x33!=0) then 
                                                                 {
                                                                      fputs("[rand_x33!=0]#",fp_executionPath) and skip;
                                                                     LData:=25;
                                                                     Mask:=127
                                                                 }
                                                                 else
                                                                 {
                                                                      fputs("[!(rand_x33!=0)]#",fp_executionPath) and skip;
                                                                     if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_57_rand_x34!=0) then 
                                                                     {
                                                                          fputs("[rand_x34!=0]#",fp_executionPath) and skip;
                                                                         LData:=26
                                                                     }
                                                                     else
                                                                     {
                                                                          fputs("[!(rand_x34!=0)]#",fp_executionPath) and skip;
                                                                         status:=15
                                                                     }
                                                                 }
                                                             }
                                                         }
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(1)]#",fp_executionPath) and skip 
                                                     };
                                                     if(status!=2) then 
                                                     {
                                                          fputs("[status!=2]#",fp_executionPath) and skip;
                                                         skip
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(status!=2)]#",fp_executionPath) and skip 
                                                     };
                                                     if(1) then 
                                                     {
                                                          fputs("[1]#",fp_executionPath) and skip;
                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35:=rand(RValue);
														   if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37:=rand(RValue);
														   if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39:=rand(RValue)
	                                                   };


                                                         if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x35!=0) then 
                                                         {
                                                              fputs("[rand_x35!=0]#",fp_executionPath) and skip;
                                                             LParity:=29
                                                         }
                                                         else
                                                         {
                                                              fputs("[!(rand_x35!=0)]#",fp_executionPath) and skip;
                                                             if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x36!=0) then 
                                                             {
                                                                  fputs("[rand_x36!=0]#",fp_executionPath) and skip;
                                                                 LParity:=31
                                                             }
                                                             else
                                                             {
                                                                  fputs("[!(rand_x36!=0)]#",fp_executionPath) and skip;
                                                                 if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x37!=0) then 
                                                                 {
                                                                      fputs("[rand_x37!=0]#",fp_executionPath) and skip;
                                                                     LParity:=33
                                                                 }
                                                                 else
                                                                 {
                                                                      fputs("[!(rand_x37!=0)]#",fp_executionPath) and skip;
                                                                     if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x38!=0) then 
                                                                     {
                                                                          fputs("[rand_x38!=0]#",fp_executionPath) and skip;
                                                                         LParity:=35
                                                                     }
                                                                     else
                                                                     {
                                                                          fputs("[!(rand_x38!=0)]#",fp_executionPath) and skip;
                                                                         if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_67_rand_x39!=0) then 
                                                                         {
                                                                              fputs("[rand_x39!=0]#",fp_executionPath) and skip;
                                                                             LParity:=37
                                                                         }
                                                                         else
                                                                         {
                                                                              fputs("[!(rand_x39!=0)]#",fp_executionPath) and skip;
                                                                             status:=15
                                                                         }
                                                                     }
                                                                 }
                                                             }
                                                         }
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(1)]#",fp_executionPath) and skip 
                                                     };
                                                     if(status!=2) then 
                                                     {
                                                          fputs("[status!=2]#",fp_executionPath) and skip;
                                                         skip
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(status!=2)]#",fp_executionPath) and skip 
                                                     };
                                                     if(1) then 
                                                     {
                                                          fputs("[1]#",fp_executionPath) and skip;
                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40:=rand(RValue);
														 if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40:=rand(RValue)
	                                                   };



                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41 and skip;
                                                        // main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41:=rand(RValue);
														 if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42:=rand(RValue);
														 if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42:=rand(RValue)
	                                                   };


                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x43 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x43:=rand(RValue);
														  if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x43) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x43:=rand(RValue)
	                                                   };


                                                         if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x40!=0) then 
                                                         {
                                                              fputs("[rand_x40!=0]#",fp_executionPath) and skip;
                                                             LStop:=32
                                                         }
                                                         else
                                                         {
                                                              fputs("[!(rand_x40!=0)]#",fp_executionPath) and skip;
                                                             if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x41!=0) then 
                                                             {
                                                                  fputs("[rand_x41!=0]#",fp_executionPath) and skip;
                                                                 if(LData!=27) then 
                                                                 {
                                                                      fputs("[LData!=27]#",fp_executionPath) and skip;
                                                                     status:=15
                                                                     
                                                                 }
                                                                 else 
                                                                 {
                                                                      fputs("[!(LData!=27)]#",fp_executionPath) and skip 
                                                                 };
                                                                 LStop:=37
                                                             }
                                                             else
                                                             {
                                                                  fputs("[!(rand_x41!=0)]#",fp_executionPath) and skip;
                                                                 if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_55_79_rand_x42!=0) then 
                                                                 {
                                                                      fputs("[rand_x42!=0]#",fp_executionPath) and skip;
                                                                     if(LData=27) then 
                                                                     {
                                                                          fputs("[LData==27]#",fp_executionPath) and skip;
                                                                         status:=15
                                                                         
                                                                     }
                                                                     else 
                                                                     {
                                                                          fputs("[!(LData==27)]#",fp_executionPath) and skip 
                                                                     };
                                                                     LStop:=33
                                                                 }
                                                                 else
                                                                 {
                                                                      fputs("[!(rand_x42!=0)]#",fp_executionPath) and skip;
                                                                     status:=15
                                                                 }
                                                             }
                                                         }
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(1)]#",fp_executionPath) and skip 
                                                     };
                                                     if(status!=2) then 
                                                     {
                                                          fputs("[status!=2]#",fp_executionPath) and skip;
                                                         skip
                                                         
                                                     }
                                                     else 
                                                     {
                                                          fputs("[!(status!=2)]#",fp_executionPath) and skip 
                                                     };
                                                     keA:=1;
                                                     keA:=0;
                                                     lock:=1;
                                                     OldIrql:=irql;
                                                     keR:=1;
                                                     keR:=0;
                                                     lock:=0;
                                                     irql:=OldIrql
                                                 }
                                                 else
                                                 {
                                                      fputs("[!(rand_x29!=0)]#",fp_executionPath) and skip;
                                                     if(main_3_rand_x30!=0) then 
                                                     {
                                                          fputs("[rand_x30!=0]#",fp_executionPath) and skip;
                                                         int main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32 and skip;
                                                         //main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32:=rand(RValue);
														   if(!feof(fp_values))then{
	                                                       fscanf(fp_values, "%d", &main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32) and skip
	                                                   }
	                                                   else{
	                                                       main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32:=rand(RValue)
	                                                   };


                                                         if(main_3_6_11_17_25_28_32_35_38_43_46_50_54_89_90_rand_x32!=0) then 
                                                         {
                                                              fputs("[rand_x32!=0]#",fp_executionPath) and skip;
                                                             status:=4
                                                             
                                                         }
                                                         else 
                                                         {
                                                              fputs("[!(rand_x32!=0)]#",fp_executionPath) and skip 
                                                         };
                                                         keA:=1;
                                                         keA:=0;
                                                         lock:=1;
                                                         OldIrql:=irql;
                                                         keR:=1;
                                                         keR:=0;
                                                         lock:=0;
                                                         irql:=OldIrql
                                                     }
                                                     else
                                                     {
                                                          fputs("[!(rand_x30!=0)]#",fp_executionPath) and skip;
                                                         if(main_3_rand_x31!=0) then 
                                                         {
                                                              fputs("[rand_x31!=0]#",fp_executionPath) and skip;
                                                             skip
                                                         }
                                                         else
                                                         {
                                                              fputs("[!(rand_x31!=0)]#",fp_executionPath) and skip;
                                                             status:=41
                                                         }
                                                     }
                                                 }
                                             }
                                         }
                                     }
                                 }
                             }
                         }
                     }
                 }
             }
         }
     }
 }
 
 }
 else 
 {
      fputs("[!(1)]#",fp_executionPath) and skip 
 };
 if(status!=7) then 
 {
      fputs("[status!=7]#",fp_executionPath) and skip;
     if(Irp!=NULL) then 
     {
          fputs("[Irp!=NULL]#",fp_executionPath) and skip;
         RemoveReferenceAndCompleteRequest(Irp,status)
         
     }
     else 
     {
          fputs("[!(Irp!=NULL)]#",fp_executionPath) and skip
     }
     
 }
 else 
 {
      fputs("[!(status!=7)]#",fp_executionPath) and skip 
 };
 RemoveReferenceForDispatch(DeviceObject)
 )
 };
  main(RValue);
  fclose(fp_executionPath) and skip;
  fclose(fp_values) and skip
 )
