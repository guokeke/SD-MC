/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2012  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.functionpointer;

import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.logging.Level;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CFACreationUtils;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CCastExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CCharLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFieldReference;
import org.sosy_lab.cpachecker.cfa.ast.c.CFloatLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializer;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSideVisitor;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CStringLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression.UnaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.DefaultCExpressionVisitor;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState.FunctionPointerTarget;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState.InvalidTarget;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState.NamedFunctionTarget;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState.UnknownTarget;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCCodeException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCFAEdgeException;
import org.sosy_lab.cpachecker.util.globalinfo.MyInfo;

@Options(prefix="cpa.functionpointer")
class FunctionPointerTransferRelation implements TransferRelation {

  private static final String FUNCTION_RETURN_VARIABLE = "__cpachecker_return_var";

  @Option(description="whether function pointers with invalid targets (e.g., 0) should be tracked in order to find calls to such pointers")
  private boolean trackInvalidFunctionPointers = false;
  private final FunctionPointerTarget invalidFunctionPointerTarget;

  private final TransferRelation wrappedTransfer;
  private final CFA functions;
  private final LogManager logger;

  FunctionPointerTransferRelation(TransferRelation pWrappedTransfer, CFA pCfa, LogManager pLogger, Configuration config) throws InvalidConfigurationException {
    config.inject(this);
    wrappedTransfer = pWrappedTransfer;
    functions = pCfa;
    logger = pLogger;

    invalidFunctionPointerTarget = trackInvalidFunctionPointers
                                   ? InvalidTarget.getInstance()
                                   : UnknownTarget.getInstance();
  }

  @Override
  public Collection<? extends AbstractState> getAbstractSuccessors(
      AbstractState pElement, Precision pPrecision, CFAEdge pCfaEdge)
      throws CPATransferException, InterruptedException {
    final FunctionPointerState oldState = (FunctionPointerState)pElement;
    Collection<FunctionPointerState> results;

    if (pCfaEdge == null) {
      CFANode node = extractLocation(oldState);
      int numLeaveEdge=node.getNumLeavingEdges();
      if(numLeaveEdge==2&&!node.isLoopStart()){
        if(!node.hasSort()){
         CFAEdge oneEdge=node.getLeavingEdge(0);
         if(oneEdge instanceof CAssumeEdge){
           List<CFAEdge> leavingEdges = node.getLeavingEdge();
           CFAEdge otherEdge=node.getLeavingEdge(1);
           if(((CAssumeEdge) oneEdge).getTruthAssumption()){
             leavingEdges.set(0, otherEdge);
             leavingEdges.set(1, oneEdge);
           }
           node.setSort(true);
         }
        }
      }
      results = new ArrayList<FunctionPointerState>(node.getNumLeavingEdges());
      for (int edgeIdx = 0; edgeIdx < node.getNumLeavingEdges(); edgeIdx++) {
        CFAEdge edge = node.getLeavingEdge(edgeIdx);
        if(edge.getLineNumber()==298){
          int g=1;
          g=g+1;
        }
        if(edge.getNotTrans()==true){
           continue;//标记为真时不用遍历该分支
        }

        int nodeNum=edge.getSuccessor().getNodeNumber();
        if(MyInfo.uselessBranches.keySet().contains(MyInfo.callstack)){
          if(MyInfo.uselessBranches.get(MyInfo.callstack).contains(nodeNum)){
            continue;
          }
        }
        if(edge instanceof CFunctionCallEdge&&!MyInfo.entry){
          MyInfo.callstack+="&"+nodeNum;
          MyInfo.entry=true;
        }
        if (!(edge instanceof FunctionPointerCallEdge)&&(!edge.getRawStatement().equals("loop")
            &&!edge.getRawStatement().equals("BLANKEDGE"))) {
          // ignore FunctionPointerCallEdges, they are from previous passes
          getAbstractSuccessorForEdge(oldState, pPrecision, edge, results);
          if(!results.isEmpty()){
            if(edge.getPredecessor() instanceof FunctionExitNode &&! MyInfo.exit){
              MyInfo.callstack=MyInfo.callstack.substring(0,MyInfo.callstack.lastIndexOf("&"));
              MyInfo.exit=true;
            }
          }
        }
      }
      // List<Integer> tempsucs=CRLGlobal.getSucnodenubs();
      /*
       * 找到CFunctionReturnEdge后继所有节点=================================龙
       */
//      for (int edgeIdx = 0; edgeIdx < node.getNumLeavingEdges(); edgeIdx++) {
//        CFAEdge edge = node.getLeavingEdge(edgeIdx);
//       int sucnodenub =  edge.getSuccessor().getNodeNumber();
//       if((edge instanceof CFunctionReturnEdge)) {
//
//        CRLGlobal.getSucnodenubs().add(sucnodenub);
//      }
//        }

      //结束找到CFunctionReturnEdge后继所有节点
//      for (int edgeIdx = 0; edgeIdx < node.getNumLeavingEdges(); edgeIdx++) {
//        CFAEdge edge = node.getLeavingEdge(edgeIdx);
//        if(edge.getRawStatement().equals("loop")){
//          continue;
//        }
//        if (!(edge instanceof FunctionPointerCallEdge)) {
//
//
//          if(edge instanceof CFunctionCallEdge){//方法调用处理========================================龙
//            CRLGlobal.getInstance().setFuncallnub(CRLGlobal.getInstance().getFuncallnub()+1);
//         int fullfuncallnub= CRLGlobal.getInstance().getFuncallnub();
//         if(fullfuncallnub==8)
//           fullfuncallnub=fullfuncallnub+1-1;
//            System.out.println("标记方法调用个数："+fullfuncallnub);
//            CRLGlobal.getInstance().setFunFlgLen(CRLGlobal.getInstance().getFunFlgLen()+1);//标记几层了
//            //System.out.println(CRLGlobal.getInstance().getFunFlgLen());
//             CRLGlobal.getLeftfunarrlenList().add(CRLGlobal.getInstance().getFunFlgLen()-1,"0");
//
//            //得到选中的参数名字，即数组名funa::b,得到b
//            FileReader fr;
//            String ps="";
//            try {
//              fr = new FileReader("D:\\property\\propositions.txt");
//              assert fr!=null;
//              BufferedReader br=new BufferedReader(fr);
//
//              String str;
//              while((str=br.readLine())!=null){
//                  ps=ps+str;
//                 // System.out.println(ps);
//              }
//              br.close();
//            } catch (FileNotFoundException e1) {
//              // TODO Auto-generated catch block
//              e1.printStackTrace();
//            } catch (IOException e) {
//              // TODO Auto-generated catch block
//              e.printStackTrace();
//            }
//            String pss=ps.substring(ps.indexOf("au=>")).trim();
//            String selectedFunnameToArrname=pss.substring(pss.indexOf("==")+2).trim();
//           //String selectedParaName=funnameToArrname.substring(funnameToArrname.indexOf("::")+2).trim();
//
//
//             //龙================================================================================加入方法调用数组长度
//            CFunctionCallEdge functionCallEdge=(CFunctionCallEdge)edge;
//            //========================================================================================只是方法调用，此方法无返回值，如fun(a)
//            if(functionCallEdge.getFunctionCall() instanceof CFunctionCallStatement){
//              CFunctionCallStatement funSta=(CFunctionCallStatement)functionCallEdge.getFunctionCall();
//              CFunctionCallExpression funExp=funSta.getFunctionCallExpression();
//              //===============
//              int parastate=-8;
//              boolean haveparaflag=false;
//              if(funExp!=null&&funExp.getDeclaration()!=null){
//              CFunctionType funparaType=(CFunctionType)funExp.getDeclaration().getType();
//              String funname=funparaType.getName();
//              System.out.println("方法名字============"+funname);
//          List<CParameterDeclaration>  xingparanames= funparaType.getParameters();
//          for(int i=0;i<xingparanames.size();i++){
//            String xingparaname=funname+"::"+xingparanames.get(i).getName();
//            if(xingparaname.trim().equals(selectedFunnameToArrname)){
//              haveparaflag=true;
//              parastate=i;
//            }
//          }
//              //==============
//
//              List<CExpression> paras=funExp.getParameterExpressions();//paras是实参
//
//              boolean addNotFlag=true;
//             if(haveparaflag){
//
//               if(paras.get(parastate) instanceof CIdExpression){
//                CIdExpression idPara=( CIdExpression)paras.get(parastate);
//                String parastr=idPara.toASTString();
//               // String paraName=idPara.getName();
//                Set<String> arrNames=CPAchecker.propositionsMap.keySet();
//                for(String arrName:arrNames){
//                  int a=arrName.indexOf("::");
//                  String changeArrName=arrName.substring(a+2).trim();
//                  if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//
//
//                 CArrayType funType=(CArrayType)idPara.getDeclaration().getType();
//                 if(funType.getType() instanceof CArrayType){//是二维数组
//
//                   String  secondLenStr= funType.getLength().toASTString();
//                   CArrayType arrArr=(CArrayType)funType.getType();
//                   String firstLenStr=arrArr.getLength().toASTString();
//                   addNotFlag=false;
//                   CRLGlobal.getFuntwoarrflag().add(true);
//                   CRLGlobal.getInstance().setFirstPointerGloLen(firstLenStr);
//                   CRLGlobal.getInstance().setFirstPointerGloLen(secondLenStr);
//                   CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//                 }else{//======================================是一维数组
//                   String arrLenValStr=funType.getLength().toASTString();
//                 addNotFlag=false;
//                 CRLGlobal.getFuntwoarrflag().add(false);
//              CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//              CRLGlobal.getInstance().setSecondPointerGloLen("one_array");
//              CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//              }
//
//                 //System.out.println(CRLGlobal.getInstance().getFunLenList());
//                // System.out.println(CPAchecker.nameToLen);
//
//                  }
//                }
//                if(addNotFlag){
//                  CRLGlobal.getFuntwoarrflag().add(false);
//
//                  CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//               // CRLGlobal.getInstance().setFunLenList("not");
//                }
//               }else if(paras.get(parastate) instanceof CUnaryExpression){//2...CUnaryExpression处理情况，包括&a[0]和结构体的&std1.sco[0]=======一般不会出来二维数组的，可以先不管
//
//
//                 CUnaryExpression idPara=( CUnaryExpression)paras.get(parastate);
//
//                 if(idPara.getOperator().name().equals("AMPER")&&(idPara.getOperand() instanceof CArraySubscriptExpression)){
//                   CArraySubscriptExpression operand=(CArraySubscriptExpression)idPara.getOperand();
//                   String paranamestr=operand.getArrayExpression().toASTString();
//                  String parasubstr= operand.getSubscriptExpression().toASTString();
//
//
//
//                 for(Map.Entry<String, String> entry:CPAchecker.nameToLen.entrySet()){
//                   String key=entry.getKey();
//                   String value=entry.getValue();
//                   int a=key.indexOf("::");
//                   String changeArrName=key.substring(a+2).trim();
//                   if(paranamestr.trim().equals(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//                     String arrLenValStr="("+value+"-"+parasubstr+")";
//                  addNotFlag=false;
//                  CRLGlobal.getFuntwoarrflag().add(false);
//               CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//               CRLGlobal.getInstance().setSecondPointerGloLen("one_array");
//               CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//
//               }
//                   }
//
//                  //System.out.println(CRLGlobal.getInstance().getFunLenList());
//                 // System.out.println(CPAchecker.nameToLen);
//
//                   }
//
//                 if(addNotFlag){
//                   CRLGlobal.getFuntwoarrflag().add(false);
//
//                   CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                // CRLGlobal.getInstance().setFunLenList("not");
//                 }
//
//
//
//
//
//
//
//               }else if(paras.get(parastate) instanceof CFieldReference){//3....CFieldReference此种情况，包括pFilter->U_tilde,pFilter是结构体指针=====得考虑二维数组和一维数组
//
//                 CFieldReference idPara=( CFieldReference)paras.get(parastate);
//                 String parastr=idPara.toASTString();//可以得到pFilter->U_tilde，整体
//                // String paraName=idPara.getName();
//                 Set<String> arrNames=CPAchecker.propositionsMap.keySet();
//                 for(String arrName:arrNames){
//                   int a=arrName.indexOf("::");
//                   String changeArrName=arrName.substring(a+2).trim();
//                   if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//
//                  //System.out.println(CPAchecker.twoLens);
//                  //System.out.println(arrName);
//                  Pair<String,String> twolen=null;
//                  boolean istwoflag=false;
//                  for(Map.Entry<String, Pair<String,String>> entry:CPAchecker.twoLens.entrySet()){
//                    String key=entry.getKey();
//                    Pair<String,String> value=entry.getValue();
//                    if(key.contains(parastr)){
//                      istwoflag=true;
//                      twolen=value;
//                      break;
//                    }
//                  }
//                // boolean istwoflag= CPAchecker.twoLens.containsKey(parastr);
//                  if(istwoflag){//是二维数组
//
//                    String  secondLenStr=twolen.getSecond() ;
//
//                    String firstLenStr=twolen.getFirst();
//                    addNotFlag=false;
//                    CRLGlobal.getFuntwoarrflag().add(true);
//                    CRLGlobal.getInstance().setFirstPointerGloLen(firstLenStr);
//                    CRLGlobal.getInstance().setSecondPointerGloLen(secondLenStr);
//                    CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//                  }else{//======================================是一维数组
//                    String arrLenValStr=CPAchecker.nameToLen.get(arrName);
//                  addNotFlag=false;
//                  CRLGlobal.getFuntwoarrflag().add(false);
//               CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//               CRLGlobal.getInstance().setSecondPointerGloLen("one_array");
//               CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//               }
//
//                  //System.out.println(CRLGlobal.getInstance().getFunLenList());
//                 // System.out.println(CPAchecker.nameToLen);
//
//                   }
//                 }
//                 if(addNotFlag){
//                   CRLGlobal.getFuntwoarrflag().add(false);
//
//                   CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                // CRLGlobal.getInstance().setFunLenList("not");
//                 }
//
//
//
//               }
//               }else{
//                 CRLGlobal.getFuntwoarrflag().add(false);
//                 CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//               // CRLGlobal.getInstance().setFunLenList("not");
//              }
//
//              }
//            }//整个if结束，没有赋值的if
//         //=======================================================================================================有返回值的方法调用，赋值，如c=fun(a);
//            else if(functionCallEdge.getFunctionCall() instanceof CFunctionCallAssignmentStatement){
//             // Map<String,Pair<String,String>> long_propositionsMap=new HashMap<String,Pair<String,String>>();
//              CFunctionCallAssignmentStatement funSta=(CFunctionCallAssignmentStatement)functionCallEdge.getFunctionCall();
//               CFunctionCallExpression funRight= funSta.getRightHandSide();
// //===============
//               int parastate=-8;
//               boolean haveparaflag=false;
//               CFunctionType funparaType=(CFunctionType)funRight.getDeclaration().getType();
//               String funname=funparaType.getName();
//               System.out.println("方法名字============"+funname);
//           List<CParameterDeclaration>  xingparanames= funparaType.getParameters();
//           for(int i=0;i<xingparanames.size();i++){
//             String xingparaname=funname+"::"+xingparanames.get(i).getName();
//             if(xingparaname.trim().equals(selectedFunnameToArrname)){
//               haveparaflag=true;
//               parastate=i;
//             }
//           }
//               //==============
//
//               boolean addNotFlag=true;
//               List<CExpression> paras=funRight.getParameterExpressions();
//              // for(CExpression para:paras){
//               if(haveparaflag){
//                  if( paras.get(parastate) instanceof CIdExpression){//=========================================1.CIdExpression
//                 CIdExpression idPara=( CIdExpression)paras.get(parastate);
//                 String parastr=idPara.toASTString();
//                // String paraName=idPara.getName();
//                 Set<String> arrNames=CPAchecker.propositionsMap.keySet();
//                 for(String arrName:arrNames){
//                   int a=arrName.indexOf("::");
//                   String changeArrName=arrName.substring(a+2).trim();
//                   if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//
//                     CVariableDeclaration funDec=(CVariableDeclaration )idPara.getDeclaration();
//                     CArrayType funType=(CArrayType)funDec.getType();
//
//                     if(funType.getType() instanceof CArrayType){//是二维数组
//
//                       String  secondLenStr= funType.getLength().toASTString();
//                       CArrayType arrArr=(CArrayType)funType.getType();
//                       String firstLenStr=arrArr.getLength().toASTString();
//                       addNotFlag=false;
//                       CRLGlobal.getFuntwoarrflag().add(true);
//                       CRLGlobal.getInstance().setFirstPointerGloLen(firstLenStr);
//                       CRLGlobal.getInstance().setSecondPointerGloLen(secondLenStr);
//                       CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//                      // System.out.println(CRLGlobal.getFunLenList());
//
//                     }else{//======================================是一维数组
//                       String arrLenValStr=funType.getLength().toASTString();
//                     addNotFlag=false;
//                     CRLGlobal.getFuntwoarrflag().add(false);
//                  CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//                  CRLGlobal.getInstance().setFirstPointerGloLen("one_array");
//                  CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//                  }
//
//                 // System.out.println(CRLGlobal.getInstance().getFunLenList());
//
//                   }
//                }
//                if(addNotFlag){
//                  CRLGlobal.getFuntwoarrflag().add(false);
//                  CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                //CRLGlobal.getInstance().setFunLenList("not");
//                }
//                  }else if(paras.get(parastate) instanceof CUnaryExpression){//2。CUnaryExpression处理情况，包括&a[0]和结构体的&std1.sco[0]=======一般不会出来二维数组的，可以先不管
//
//
//
//                    CUnaryExpression idPara=( CUnaryExpression)paras.get(parastate);
//
//                    if(idPara.getOperator().name().equals("AMPER")&&(idPara.getOperand() instanceof CArraySubscriptExpression)){
//                      CArraySubscriptExpression operand=(CArraySubscriptExpression)idPara.getOperand();
//                      String paranamestr=operand.getArrayExpression().toASTString();
//                     String parasubstr= operand.getSubscriptExpression().toASTString();
//
//
//
//                    for(Map.Entry<String, String> entry:CPAchecker.nameToLen.entrySet()){
//                      String key=entry.getKey();
//                      String value=entry.getValue();
//                      int a=key.indexOf("::");
//                      String changeArrName=key.substring(a+2).trim();
//                      if(paranamestr.trim().equals(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//                       String arrLenValStr="("+value+"-"+parasubstr+")";
//                     addNotFlag=false;
//                     CRLGlobal.getFuntwoarrflag().add(false);
//                  CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//                  CRLGlobal.getInstance().setSecondPointerGloLen("one_array");
//                  CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//
//                  }
//                      }
//
//                     //System.out.println(CRLGlobal.getInstance().getFunLenList());
//                    // System.out.println(CPAchecker.nameToLen);
//
//                      }
//
//                    if(addNotFlag){
//                      CRLGlobal.getFuntwoarrflag().add(false);
//
//                      CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                   // CRLGlobal.getInstance().setFunLenList("not");
//                    }
//
//
//
//
//
//
//
//
//
//
//                  }else if(paras.get(parastate) instanceof CFieldReference){//3。CFieldReference此种情况，包括pFilter->U_tilde,pFilter是结构体指针=====得考虑二维数组和一维数组
//
//                    CFieldReference idPara=( CFieldReference)paras.get(parastate);
//                    String parastr=idPara.toASTString();//可以得到pFilter->U_tilde，整体
//                   // String paraName=idPara.getName();
//                    Set<String> arrNames=CPAchecker.propositionsMap.keySet();
//                    for(String arrName:arrNames){
//                      int a=arrName.indexOf("::");
//                      String changeArrName=arrName.substring(a+2).trim();
//                      if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入
//
//                    // System.out.println(CPAchecker.twoLens);
//                     //System.out.println(arrName);
//                     Pair<String,String> twolen=null;
//                     boolean istwoflag=false;
//                     for(Map.Entry<String, Pair<String,String>> entry:CPAchecker.twoLens.entrySet()){
//                       String key=entry.getKey();
//                       Pair<String,String> value=entry.getValue();
//                       if(key.contains(parastr)){
//                         istwoflag=true;
//                         twolen=value;
//                         break;
//                       }
//                     }
//                   // boolean istwoflag= CPAchecker.twoLens.containsKey(parastr);
//                     if(istwoflag){//是二维数组
//
//                       String  secondLenStr=twolen.getSecond() ;
//
//                       String firstLenStr=twolen.getFirst();
//                       addNotFlag=false;
//                       CRLGlobal.getFuntwoarrflag().add(true);
//                       CRLGlobal.getInstance().setFirstPointerGloLen(firstLenStr);
//                       CRLGlobal.getInstance().setSecondPointerGloLen(secondLenStr);
//                       CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//                     }else{//======================================是一维数组
//                       //System.out.println(CPAchecker.nameToLen);
//                       String arrLenValStr=null;
//                       for(Map.Entry<String,String> entry:CPAchecker.nameToLen.entrySet()){
//                         String key=entry.getKey();
//                         String value=entry.getValue();
//                         if(key.contains(parastr)){
//                           arrLenValStr=value;
//                           break;
//                         }
//                       }
//
//                     addNotFlag=false;
//                     CRLGlobal.getFuntwoarrflag().add(false);
//                  CRLGlobal.getInstance().setFirstPointerGloLen(arrLenValStr);
//                  CRLGlobal.getInstance().setSecondPointerGloLen("one_array");
//                  CRLGlobal.getFunLenList().add(Pair.of(CRLGlobal.getInstance().getFirstPointerGloLen(), CRLGlobal.getInstance().getSecondPointerGloLen()));
//
//                  }
//
//                     //System.out.println(CRLGlobal.getInstance().getFunLenList());
//                    // System.out.println(CPAchecker.nameToLen);
//
//                      }
//                    }
//                    if(addNotFlag){
//                      CRLGlobal.getFuntwoarrflag().add(false);
//
//                      CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                   // CRLGlobal.getInstance().setFunLenList("not");
//                    }
//
//
//
//                  }
//                   }else{
//                     CRLGlobal.getFuntwoarrflag().add(false);
//                   CRLGlobal.getInstance();
//                    // System.out.println(CRLGlobal.getInstance().getFunFlgLen());
//                   CRLGlobal.getFunLenList().add(Pair.of("not", "not"));
//                    // CRLGlobal.getInstance().setFunLenList("not");
//                   }
//            }
//            getAbstractSuccessorForEdge(oldState, pPrecision, edge, results);
//            }
//
//
//
//
//          else if(edge instanceof CStatementEdge){//=====================================================================================================指针指向的数组处理
//            //提取选择的指针名字
//            FileReader fr;
//            String ps="";
//            try {
//              fr = new FileReader("D:\\property\\propositions.txt");
//              assert fr!=null;
//              BufferedReader br=new BufferedReader(fr);
//
//              String str;
//              while((str=br.readLine())!=null){
//                  ps=ps+str;
//                 // System.out.println(ps);
//              }
//              br.close();
//            } catch (FileNotFoundException e1) {
//              // TODO Auto-generated catch block
//              e1.printStackTrace();
//            } catch (IOException e) {
//              // TODO Auto-generated catch block
//              e.printStackTrace();
//            }
//           String selectedPointerName= ps.substring(ps.indexOf("::")+2, ps.indexOf(" ")).trim();
//            CStatementEdge statementEdge=(CStatementEdge)edge;
//            CStatement expression= statementEdge.getStatement();
//            if(expression instanceof CAssignment){
//              CAssignment assignmentExpression=(CAssignment)expression;
//              CExpression op1=assignmentExpression.getLeftHandSide();//得到左边op1
//              CRightHandSide op2= assignmentExpression.getRightHandSide();//得到右边op2
//              //加入临时数组名加减法变动
//              String myop1str=op1.toASTString().trim();
//              String myop2str=op2.toASTString().trim();
//              String myfunname=node.getFunctionName();
//              String mystr=myfunname+"::"+myop1str;
//              if(CPAchecker.nameToLen.containsKey(mystr)){
//                if(!CPAchecker.nameToLen.get(mystr).equals("pointer_array")){
//                  String repname=myop1str.replaceAll("\\.", "\\\\.");
//                  repname=repname.replaceAll("\\(", "\\\\(");
//                  repname=repname.replaceAll("\\)", "\\\\)");
//                String templen=  myop2str.replaceAll(repname, "0");
//                CRLGlobal.getInstance().setTempleftarraynamelen(templen);
//                int temp=CRLGlobal.getInstance().getFunFlgLen();
//
//                CRLGlobal.getLeftfunarrlenList().add(temp-1,CRLGlobal.getInstance().getTempleftarraynamelen());
//                }
//
//              }
//              if(op1 instanceof CIdExpression){
//                CIdExpression op1IdExp=(CIdExpression)op1;
//                if((op1IdExp.getExpressionType() instanceof CPointerType)){//op1是指针形式
//                 String op1PointerName= op1IdExp.getName();
//                 String op1funcname=node.getFunctionName();
//                 String op1fullname=op1funcname+"::"+op1PointerName;
//                  String op2Str= op2.toASTString();
//                  String op2StrNoSpace=op2Str.replaceAll(" ", "");
//                  if(op1PointerName.trim().equals(selectedPointerName)&&CPAchecker.nameToLen.keySet().contains(op1fullname)&&CPAchecker.nameToLen.get(op1fullname).equals("pointer_array")){//左边相等,左边是选中的指针==============分形式====a和a+此两种形式
//
//                    if((op2.getExpressionType() instanceof CPointerType)&&(op2 instanceof CIdExpression)){//第四种情形==========p=q注意没有考虑  q+1等形式,
//                      CIdExpression op2IdExp=(CIdExpression)op2;
//                      String arrNameop2=op2IdExp.getName();
//                      String  function=node.getFunctionName();
//                      String exArrName=function+"::"+arrNameop2;
//                     Set<String> firstPointerToLens= CPAchecker.long_firstNameToPureLen.keySet();
//                      if(firstPointerToLens.contains(exArrName)){//看有没有在first中,如果在，提取length，把下标变量清零
//                        String poinerArrLength=CPAchecker.long_firstNameToPureLen.get(exArrName);
//                        CRLGlobal.getInstance().setPointerGloLenZero();
//
//                        CRLGlobal.getInstance().setPointerArrFullLen(poinerArrLength);
//
//                      }
//
//                    }else{
//                      Set<String> nameKeys=CPAchecker.pureNameLen.keySet();
//                      String fullnameKey=null;
//                      String purenameKey=null;
//                      boolean flag2=false;
//                     boolean flag1=false;
//
//
//                    for(String nameKey:nameKeys){
//                      int a=nameKey.indexOf("::");
//                     String nameKey1=nameKey.substring(a+2).trim();
//                     if(op2StrNoSpace.matches(nameKey1.trim()+"\\+.*")||op2StrNoSpace.matches(".*\\+"+nameKey1.trim())){
//                       flag2=true;
//                       fullnameKey=nameKey;
//                       purenameKey=nameKey1;
//                     }
//                     if(op2Str.trim().equals(nameKey1)){
//                       flag1=true;
//                       fullnameKey=nameKey;
//                       purenameKey=nameKey1;
//                     }
//
//                     }
//                      String poinerArrLength;
//                      if(flag1){//第一种形式====================p=a==把length提出来，把下标变量清零
//                        poinerArrLength= CPAchecker.pureNameLen.get(fullnameKey);
//                        CRLGlobal.getInstance().setPointerGloLenZero();
//                        CRLGlobal.getInstance().setPointerGloLen(CRLGlobal.getInstance().getPointerGloLen());
//
//                       CRLGlobal.getInstance().setPointerArrFullLen(poinerArrLength);
//                       //System.out.println(CRLGlobal.getInstance().getPointerArrFullLen());
//
//                      }
//                      else if(flag2){//第二种形式========p=a+1==把length提出来，把下标清零，再把op2Str中a换0赋值给下标变量
//                         poinerArrLength= CPAchecker.pureNameLen.get(fullnameKey);
//                        CRLGlobal.getInstance().setPointerGloLenZero();
//                        String op2StrRep=op2Str.replaceAll(purenameKey, "0");
//                        op2StrRep=op2StrRep+"+("+CRLGlobal.getInstance().getTempleftarraynamelen()+")";
//                        CRLGlobal.getInstance().setPointerGloLen(op2StrRep);
//
//
//
//                      }
//                      else  if(op2StrNoSpace.matches(op1PointerName.trim()+"\\+.*")||op2StrNoSpace.matches(".*\\+"+op1PointerName.trim())||op2StrNoSpace.matches(op1PointerName.trim()+"\\-.*")||op2StrNoSpace.matches(".*\\-"+op1PointerName.trim())){//第三种形式====p=p+或p=p-此种形式，把把op2Str中p+P-中p换成0赋值给下标变量
//                        String op2StrReplace= op2Str.replaceAll(op1PointerName, "0");
//                        CRLGlobal.getInstance().setPointerGloLen(op2StrReplace);
//                       }else{//第五种形式，即上面都不是的时候，如果p指向了变量地址等，则把长度变成"noPointerArrLen"
//                         CRLGlobal.getInstance().setPointerArrFullLen("noPointerArrLen");
//
//                       }
//
//
//
//                  }
//
//                  }//左边相等结束==============得处理右边是指针p即可以是
//
//
//                }//指针结束
//            }
//
//
//            }
//
//
//            // System.out.println("00000000000000");
//         getAbstractSuccessorForEdge(oldState, pPrecision, edge, results);
//          }
//
//
//          else{
//            //龙==================================================================================之间都是加入的================结束
//         // ignore FunctionPointerCallEdges, they are from previous passes
//            getAbstractSuccessorForEdge(oldState, pPrecision, edge, results);
//          }
//
//
//
//          }
//
//      }

    } else {
      results = new ArrayList<FunctionPointerState>(1);
      getAbstractSuccessorForEdge(oldState, pPrecision, pCfaEdge, results);

    }
    return results;
  }

  private void getAbstractSuccessorForEdge(
      FunctionPointerState oldState, Precision pPrecision, CFAEdge pCfaEdge, Collection<FunctionPointerState> results)
      throws CPATransferException, InterruptedException {
    CFAEdge cfaEdge;
    // first, check if this is a function pointer call
    String functionCallVariable = getFunctionPointerCall(pCfaEdge);
    if (functionCallVariable != null) {
      // this is indeed a function call via a function pointer

      FunctionPointerTarget target = oldState.getTarget(functionCallVariable);
      if (target instanceof NamedFunctionTarget) {
        String functionName = ((NamedFunctionTarget)target).getFunctionName();
        FunctionEntryNode fDefNode = functions.getFunctionHead(functionName);
        if (fDefNode != null) {
          logger.log(Level.FINEST, "Function pointer", functionCallVariable, "points to", target, "while it is used.");

          CStatementEdge edge = (CStatementEdge)pCfaEdge;
          CFunctionCall functionCall = (CFunctionCall)edge.getStatement();
          CFANode predecessorNode = edge.getPredecessor();
          CFANode successorNode = edge.getSuccessor();
          int lineNumber = edge.getLineNumber();

          FunctionExitNode fExitNode = fDefNode.getExitNode();

          // Create new edges.
          CFunctionSummaryEdge calltoReturnEdge = new CFunctionSummaryEdge(edge.getRawStatement(),
              lineNumber, predecessorNode, successorNode, functionCall);

          FunctionPointerCallEdge callEdge = new FunctionPointerCallEdge(edge.getRawStatement(), lineNumber, predecessorNode, (CFunctionEntryNode)fDefNode, functionCall, calltoReturnEdge);
          predecessorNode.addLeavingEdge(callEdge);
          fDefNode.addEnteringEdge(callEdge);

          if (fExitNode.getNumEnteringEdges() > 0) {
            FunctionPointerReturnEdge returnEdge = new FunctionPointerReturnEdge(lineNumber, fExitNode, successorNode, callEdge, calltoReturnEdge);
            fExitNode.addLeavingEdge(returnEdge);
            successorNode.addEnteringEdge(returnEdge);

          } else {
            // exit node of called functions is not reachable, i.e. this function never returns
            // no need to add return edges
          }

          // now substitute the real edge with the fake edge
          cfaEdge = callEdge;
        } else {
          throw new UnrecognizedCCodeException("function pointer points to unknown function " + functionName, pCfaEdge);
        }

      } else if (target instanceof UnknownTarget) {
        // we known nothing, so just keep the old edge
        cfaEdge = pCfaEdge;

      } else if (target instanceof InvalidTarget) {
        throw new UnrecognizedCCodeException("function pointer points to invalid memory address", pCfaEdge);
      } else {
        throw new AssertionError();
      }

    } else {
      // use the real edge
      cfaEdge = pCfaEdge;
    }

    // Some CPAs rely on the call-to-return edge when processing the return edge.
    // We add it here to the CFA and remove it before returning from this function.
    if (cfaEdge instanceof FunctionPointerReturnEdge) {
      CFunctionSummaryEdge calltoReturnEdge = ((FunctionPointerReturnEdge) cfaEdge).getSummaryEdge();
      calltoReturnEdge.getPredecessor().addLeavingSummaryEdge(calltoReturnEdge);
      calltoReturnEdge.getSuccessor().addEnteringSummaryEdge(calltoReturnEdge);
    }

    // now handle the edge, whether it is real or not
    //System.out.println("wrappedTransfer=>"+wrappedTransfer);
    Collection<? extends AbstractState> newWrappedStates = wrappedTransfer.getAbstractSuccessors(oldState.getWrappedState(), pPrecision, cfaEdge);
    //oldState.setTerminal(((CompositeState)(oldState.getWrappedState())).getTerminal());//mycode
    for (AbstractState newWrappedState : newWrappedStates) {
      FunctionPointerState.Builder newState = oldState.createBuilderWithNewWrappedState(newWrappedState);

      newState = handleEdge(newState, cfaEdge);

      if (newState != null) {
        results.add(newState.build());
      }
    }

    if (pCfaEdge instanceof FunctionPointerReturnEdge) {
      // We are returning from a function that was called via a function pointer
      // Remove all fake edges we have created.

      FunctionPointerReturnEdge returnEdge = (FunctionPointerReturnEdge)pCfaEdge;

      // The call edge and the return edge are never removed from the CFA,
      // because we might need them for refinement.
      // CallstackCPA should force taking the right return edge.

      CFACreationUtils.removeSummaryEdgeFromNodes(returnEdge.getSummaryEdge());
    }
  }

  private String getFunctionPointerCall(CFAEdge pCfaEdge) throws UnrecognizedCCodeException {
    if (pCfaEdge.getEdgeType() != CFAEdgeType.StatementEdge) {
      return null;
    }

    CStatement statement = ((CStatementEdge)pCfaEdge).getStatement();
    if (!(statement instanceof CFunctionCall)) {
      return null;
    }

    CFunctionCallExpression funcCall = ((CFunctionCall)statement).getFunctionCallExpression();
    CExpression nameExp = funcCall.getFunctionNameExpression();
    String currentFunction = pCfaEdge.getPredecessor().getFunctionName();

    // functions may be called either as f() or as (*f)(),
    // so remove the star operator if its there
    if (nameExp instanceof CUnaryExpression) {
      CUnaryExpression unaryExp = (CUnaryExpression)nameExp;
      if (unaryExp.getOperator() == UnaryOperator.STAR) {
        // a = (*f)(b)
        nameExp = unaryExp.getOperand();

      } else {
        throw new UnrecognizedCCodeException("unknown function call expression", pCfaEdge, nameExp);
      }
    }

    if (nameExp instanceof CIdExpression) {
      // a = f(b) or a = (*f)(b)
      return scopedIfNecessary((CIdExpression)nameExp, currentFunction);
    } else if (nameExp instanceof CFieldReference) {
      // TODO This is a function pointer call "(s->f)()" or "(s.f)()"
      return null;
    } else if (nameExp instanceof CArraySubscriptExpression) {
      // TODO This is a function pointer call (*a[i])()
      return null;
    }  else {
      throw new UnrecognizedCCodeException("unknown function call expression", pCfaEdge, nameExp);
    }
  }

  private FunctionPointerState.Builder handleEdge(FunctionPointerState.Builder newState, CFAEdge pCfaEdge) throws CPATransferException {

    switch (pCfaEdge.getEdgeType()) {

      // declaration of a function pointer.
      case DeclarationEdge: {
        CDeclarationEdge declEdge = (CDeclarationEdge) pCfaEdge;
        handleDeclaration(newState, declEdge);
        break;
      }

      // if edge is a statement edge, e.g. a = b + c
      case StatementEdge: {
        CStatementEdge statementEdge = (CStatementEdge) pCfaEdge;
        handleStatement(newState, statementEdge.getStatement(), pCfaEdge);
        break;
      }

      case FunctionCallEdge: {
        CFunctionCallEdge functionCallEdge = (CFunctionCallEdge) pCfaEdge;
        handleFunctionCall(newState, functionCallEdge);
        break;
      }

      case ReturnStatementEdge: {
        CReturnStatementEdge returnStatementEdge = (CReturnStatementEdge)pCfaEdge;
        handleReturnStatement(newState, returnStatementEdge.getExpression(), pCfaEdge);
        break;
      }

      case FunctionReturnEdge: {
        CFunctionReturnEdge functionReturnEdge = (CFunctionReturnEdge) pCfaEdge;
        handleFunctionReturn(newState, functionReturnEdge);
        break;
      }

      // maybe two function pointers are compared.
      case AssumeEdge: {
        break;
      }

      // nothing to do.

      case BlankEdge:
      case CallToReturnEdge: {
        break;
      }

      default:
        throw new UnrecognizedCFAEdgeException(pCfaEdge);
    }

    return newState;
  }

  private void handleDeclaration(FunctionPointerState.Builder pNewState, CDeclarationEdge declEdge) throws UnrecognizedCCodeException {

    if (!(declEdge.getDeclaration() instanceof CVariableDeclaration)) {
      // not a variable declaration
      return;
    }
    CVariableDeclaration decl = (CVariableDeclaration)declEdge.getDeclaration();

    String functionName = declEdge.getPredecessor().getFunctionName();

    // get name of declaration
    String name = decl.getName();
    if (name == null) {
      // not a variable declaration
      return;
    }
    if (!decl.isGlobal()) {
      name = scoped(name, functionName);
    }

    // get initial value
    FunctionPointerTarget initialValue = invalidFunctionPointerTarget;

    if (decl.getInitializer() != null) {
      CInitializer init = decl.getInitializer();
      if (init instanceof CInitializerExpression) {
        initialValue = getValue(((CInitializerExpression) init).getExpression(), pNewState, functionName);
      }
    }

    // store declaration in abstract state
    pNewState.setTarget(name, initialValue);
  }

  private void handleStatement(FunctionPointerState.Builder pNewState, CStatement pStatement,
        CFAEdge pCfaEdge) throws UnrecognizedCCodeException {

    if (pStatement instanceof CAssignment) {
      // assignment like "a = b" or "a = foo()"
      String functionName = pCfaEdge.getPredecessor().getFunctionName();

      CAssignment assignment = (CAssignment)pStatement;
      String varName = getLeftHandSide(assignment.getLeftHandSide(), pCfaEdge, functionName);

      if (varName != null) {
        FunctionPointerTarget target = getValue(assignment.getRightHandSide(), pNewState, functionName);
        pNewState.setTarget(varName, target);
      }

    } else if (pStatement instanceof CFunctionCallStatement) {
      // external function call without return value

    } else if (pStatement instanceof CExpressionStatement) {
      // side-effect free statement

    } else {
      throw new UnrecognizedCCodeException(pCfaEdge, pStatement);
    }
  }

  private void handleFunctionCall(FunctionPointerState.Builder pNewState, CFunctionCallEdge callEdge) throws UnrecognizedCCodeException {

    CFunctionEntryNode functionEntryNode = callEdge.getSuccessor();
    String calledFunctionName = functionEntryNode.getFunctionName();
    String callerFunctionName = callEdge.getPredecessor().getFunctionName();

    List<String> paramNames = functionEntryNode.getFunctionParameterNames();
    List<CExpression> arguments = callEdge.getArguments();

    if (functionEntryNode.getFunctionDefinition().getType().takesVarArgs()) {
      if (paramNames.size() > arguments.size()) {
        throw new UnrecognizedCCodeException("Number of parameters on function call does " +
            "not match function definition", callEdge);
      }

    } else {
      if (paramNames.size() != arguments.size()) {
        throw new UnrecognizedCCodeException("Number of parameters on function call does " +
            "not match function definition", callEdge);
      }
    }

    // used to get value in caller context
    ExpressionValueVisitor v = new ExpressionValueVisitor(pNewState, callerFunctionName, invalidFunctionPointerTarget);

    for (int i=0; i < paramNames.size(); i++) {
      String paramName = scoped(paramNames.get(i), calledFunctionName);
      CExpression actualArgument = arguments.get(i);

      FunctionPointerTarget target = actualArgument.accept(v);
      pNewState.setTarget(paramName, target);

      // TODO only do this if declared type is function pointer?
    }
  }

  private void handleReturnStatement(FunctionPointerState.Builder pNewState, CExpression returnValue,
      CFAEdge pCfaEdge) throws UnrecognizedCCodeException {

    if (returnValue != null) {
      String functionName = pCfaEdge.getPredecessor().getFunctionName();
      FunctionPointerTarget target = getValue(returnValue, pNewState, functionName);

      pNewState.setTarget(FUNCTION_RETURN_VARIABLE, target);
    }
  }


  private void handleFunctionReturn(FunctionPointerState.Builder pNewState, CFunctionReturnEdge pFunctionReturnEdge) throws UnrecognizedCCodeException {
    CFunctionSummaryEdge summaryEdge = pFunctionReturnEdge.getSummaryEdge();
    assert summaryEdge != null;

    CFunctionCall funcCall = summaryEdge.getExpression();
    if (funcCall instanceof CFunctionCallAssignmentStatement) {

      CExpression left = ((CFunctionCallAssignmentStatement)funcCall).getLeftHandSide();

      String callerFunction = summaryEdge.getSuccessor().getFunctionName();
      String varName = getLeftHandSide(left, summaryEdge, callerFunction);

      if (varName != null) {

        FunctionPointerTarget target = pNewState.getTarget(FUNCTION_RETURN_VARIABLE);
        pNewState.setTarget(varName, target);
      }
    }

    // clear special variable
    pNewState.setTarget(FUNCTION_RETURN_VARIABLE, UnknownTarget.getInstance());

    // clear all local variables of inner function
    String calledFunction = pFunctionReturnEdge.getPredecessor().getFunctionName();
    pNewState.clearVariablesWithPrefix(calledFunction + "::");
  }

  private String getLeftHandSide(CExpression lhsExpression, CFAEdge edge, String functionName) throws UnrecognizedCCodeException {

    if (lhsExpression instanceof CIdExpression) {
      // a = ...
      return scopedIfNecessary((CIdExpression)lhsExpression, functionName);

    } else if (lhsExpression instanceof CUnaryExpression
        && ((CUnaryExpression)lhsExpression).getOperator() == UnaryOperator.STAR) {
      // *a = ...
      // TODO: Support this statement.

    } else if (lhsExpression instanceof CFieldReference) {

      //String functionName = pCfaEdge.getPredecessor().getFunctionName();
      //handleAssignmentToVariable(op1.getRawSignature(), op2, v);

      // TODO: Support this statement.

    } else if (lhsExpression instanceof CArraySubscriptExpression) {
      // TODO assignment to array cell

    } else {
      throw new UnrecognizedCCodeException("left operand of assignment has to be a variable", edge, lhsExpression);
    }
    return null;
  }

  private FunctionPointerTarget getValue(CRightHandSide exp, FunctionPointerState.Builder element, String function) throws UnrecognizedCCodeException {
    return exp.accept(new ExpressionValueVisitor(element, function, invalidFunctionPointerTarget));
  }

  private static class ExpressionValueVisitor extends DefaultCExpressionVisitor<FunctionPointerTarget, UnrecognizedCCodeException>
                                              implements CRightHandSideVisitor<FunctionPointerTarget, UnrecognizedCCodeException> {

    private final FunctionPointerState.Builder state;
    private final String function;
    private final FunctionPointerTarget targetForInvalidPointers;

    private ExpressionValueVisitor(FunctionPointerState.Builder pElement, String pFunction,
                                   FunctionPointerTarget pTargetForInvalidPointers) {
      state = pElement;
      function = pFunction;
      targetForInvalidPointers = pTargetForInvalidPointers;
    }

    @Override
    public FunctionPointerTarget visit(CUnaryExpression pE) {
      if ((pE.getOperator() == UnaryOperator.AMPER) && (pE.getOperand() instanceof CIdExpression)) {
        CIdExpression operand = (CIdExpression)pE.getOperand();
        return new NamedFunctionTarget(operand.getName());

      } else {
        return visitDefault(pE);
      }
    }

    @Override
    public FunctionPointerTarget visit(CIdExpression pE) {
      return state.getTarget(scopedIfNecessary(pE, function));
    }

    @Override
    public FunctionPointerTarget visit(CCastExpression pE) throws UnrecognizedCCodeException {
      return pE.getOperand().accept(this);
    }

    @Override
    protected FunctionPointerTarget visitDefault(CExpression pExp) {
      return UnknownTarget.getInstance();
    }

    @Override
    public FunctionPointerTarget visit(CFunctionCallExpression pIastFunctionCallExpression) {
      return UnknownTarget.getInstance();
    }

    @Override
    public FunctionPointerTarget visit(CCharLiteralExpression pE) {
      return targetForInvalidPointers;
    }

    @Override
    public FunctionPointerTarget visit(CFloatLiteralExpression pE) {
      return targetForInvalidPointers;
    }

    @Override
    public FunctionPointerTarget visit(CIntegerLiteralExpression pE) {
      return targetForInvalidPointers;
    }

    @Override
    public FunctionPointerTarget visit(CStringLiteralExpression pE) {
      return targetForInvalidPointers;
    }
  }

  // looks up the variable in the current namespace
  private static String scopedIfNecessary(CIdExpression var, String function) {
    CSimpleDeclaration decl = var.getDeclaration();
    boolean isGlobal = false;
    if (decl instanceof CDeclaration) {
      isGlobal = ((CDeclaration)decl).isGlobal();
    }

    if (isGlobal) {
      return var.getName();
    } else {
      return scoped(var.getName(), function);
    }
  }

  // prefixes function to variable name
  // Call only if you are sure you have a local variable!
  private static String scoped(String var, String function) {
    return function + "::" + var;
  }

  @Override
  public Collection<? extends AbstractState> strengthen(
      AbstractState pElement, List<AbstractState> pOtherElements,
      CFAEdge pCfaEdge, Precision pPrecision) {
    // in this method we could access the abstract domains of other CPAs
    // if required.
    return null;
  }
}