/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.xidian.cpachecker.dz.proposition;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CParser;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CComplexTypeDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CTypeDefDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression.UnaryOperator;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CArrayType;
import org.sosy_lab.cpachecker.cfa.types.c.CCompositeType;
import org.sosy_lab.cpachecker.cfa.types.c.CElaboratedType;
import org.sosy_lab.cpachecker.cfa.types.c.CFunctionType;
import org.sosy_lab.cpachecker.cfa.types.c.CNamedType;
import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cfa.types.c.CCompositeType.CCompositeTypeMemberDeclaration;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.xidian.cpachecker.dz.Proposition;
import org.xidian.crl.CRLGlobal;


public class PropositionInfo {
  private static PropositionInfo instance;
  public static CParser parser = null;
  private Map<String, Pair<String, String>> propositionsMap=new HashMap<String, Pair<String, String>>();
  private Map<String,Pair<String,String>> proLeftSide=new HashMap<String,Pair<String,String>>();
  //private Set<Pair<String,String>> vars=new HashSet<Pair<String,String>>();
   private  PropositionInfo(){

   }
   public static PropositionInfo getInstance() {
     if (instance == null) {
       instance = new PropositionInfo();
     }
     return instance;
   }
   public Map<String, Pair<String, String>> getPropositionsMap(){
     return propositionsMap;
   }


  public Map<String, Pair<String, String>> getProLeftSide() {
    return proLeftSide;
  }

  public void setProLeftSide(Map<String, Pair<String, String>> pProLeftSide) {
    proLeftSide = pProLeftSide;
  }
  public static List<Map<Pair<String,String>,CFAEdge>> long_propositionToCFAEdge(Proposition proposition,CFAEdge edge) throws ParserException{
    Map<Pair<String,String>,String> props=proposition.getPropositions();
    String arrSubVal = null;//注意：初试化问题，给下面的secondT=secondT.replaceAll(arrName,String.valueOf(arrSubVal));有关，必须初始化
    String  arrLen=null;
    String arrName = null;
    boolean funFlag=false;
    List<Map<Pair<String,String>,CFAEdge>> dNotDEdges=new ArrayList<Map<Pair<String,String>,CFAEdge>>();
    List<Pair<String,String>>  subToLenNums = new ArrayList<Pair<String,String>>();
    Pair<String,String> subToLenNub;


    //得到选择的数组的     方法名：：数组名     字符串
    FileReader fr;
    String ps="";
    try {
      fr = new FileReader("D:\\property\\propositions.txt");
      assert fr!=null;
      BufferedReader br=new BufferedReader(fr);

      String str;
      while((str=br.readLine())!=null){
          ps=ps+str;
         // System.out.println(ps);
      }
      br.close();
    } catch (FileNotFoundException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    String pss=ps.substring(ps.indexOf("au=>")).trim();
    String funnameToArrname=pss.substring(pss.indexOf("==")+2).trim();
    //找到选择的数组名所对应的数组长度
    String funStrLen=CPAchecker.nameToLen.get(funnameToArrname);
    //得到选中数组的名字
    arrName=funnameToArrname.substring(funnameToArrname.indexOf("::")+2).trim();




    //得到数组名称和下标值=================================================================龙开始
    //通过functionCallEdge得到的=========================2
    if(funStrLen.equals("function_parameter_array")){
      // System.out.println(CRLGlobal.getInstance().getFunLenList());
      int temp=CRLGlobal.getInstance().getFunFlgLen();
      Pair<String,String> arrLens=CRLGlobal.getFunLenList().get(temp-1);
      String firstLenStr=arrLens.getFirst();
      String secondLenStr=arrLens.getSecond();

        if(CRLGlobal.getInstance().getFunFlgLen()>0){
          if(secondLenStr.equals("one_array")){//=========================================================一维数组方法参数处理
          //得到数组长度
          //System.out.println(CRLGlobal.getInstance().getFunFlgLen());
          //System.out.println(CRLGlobal.getInstance().getFunLenList());

        arrLen=  firstLenStr+"+"+CRLGlobal.getLeftfunarrlenList().get(temp-1);
        switch(edge.getEdgeType()){
        case AssumeEdge://待解决========================================================1.AssumeEdge
          CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
          CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
          String assumeedgestr= binaryExp.toASTString();
          ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
          myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
          for(String mysublen:myAllAssuSubLens){
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }

          break;
        case StatementEdge://得到数组下标===============================================2.StatementEdge
          CStatementEdge statementEdge=(CStatementEdge)edge;
          CStatement expression=statementEdge.getStatement();
          if(expression instanceof CAssignment){
            CAssignment assignmentExp=(CAssignment)expression;
            CExpression op1=assignmentExp.getLeftHandSide();
            CRightHandSide op2=  assignmentExp.getRightHandSide();
            String op2str=op2.toASTString();
            String op1str=op1.toASTString();
            String str=op1str+"="+op2str;

            if(op1 instanceof CArraySubscriptExpression){
              /*CIdExpression arrSubExp=(CIdExpression)((CArraySubscriptExpression) op1).getArrayExpression();
               arrSubVal=((CArraySubscriptExpression) op1).getSubscriptExpression().toASTString();
               subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
               ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
               myAllSubLens=getAllArrLens(str,arrName);
               for(String mysublen:myAllSubLens){

                 subToLenNums.add(Pair.of(mysublen,arrLen ));
               }
            }

            else if(op1 instanceof CUnaryExpression){
             UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();
             switch(unaryOperator){
             case STAR:
               CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
             BinaryOperator starOperator=  unaryOperand.getOperator();
             switch(starOperator){
             case PLUS:
             /*String  subVal=  unaryOperand.getOperand2().toASTString();
             arrSubVal="("+subVal+")";
             subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
             myAllSubLens=getAllArrLens(str,arrName);
             for(String mysublen:myAllSubLens){

               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }
             }
            }
           }else{
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
             myAllSubLens=getAllArrLens(op2str,arrName);
             for(String mysublen:myAllSubLens){

               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }
           }


          }//赋值if结束CAssignment
          break;
          default://===========================================================================3.其他语句
            String str= edge.toString();
            ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
            myAllSubLens=getAllArrLens(str,arrName);
            for(String mysublen:myAllSubLens){
              subToLenNums.add(Pair.of(mysublen,arrLen ));
            }
            break;

        }


        }else{//=============================================================================================二维数组参数处理

          //得到数组长度
          //System.out.println(CRLGlobal.getInstance().getFunFlgLen());
          //System.out.println(CRLGlobal.getInstance().getFunLenList());


              List<Pair<String,String>> subtwolens=CFAUtils.subTwoLens;
             String firstfullval= firstLenStr;//得到第一个fulllen
             String secondfullval=secondLenStr;//得到第二个fulllen
             for(Pair<String,String> mysubtwolen:subtwolens){
               String firstsublen=mysubtwolen.getFirst();
               String secondsublen=mysubtwolen.getSecond();
               subToLenNums.add(Pair.of(firstsublen, firstfullval));
               subToLenNums.add(Pair.of(secondsublen, secondfullval));
             }
            }






        }



    }//结束第一个if
    else if(funStrLen.equals("pointer_array")){
      arrLen=CRLGlobal.getInstance().getPointerArrFullLen();//得到当前长度
     String tempArrSubVal= CRLGlobal.getInstance().getPointerGloLen();//得到下标临时长度，即上面p的值
     switch(edge.getEdgeType()){
     case AssumeEdge:
       CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
       CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
       String assumeedgestr= binaryExp.toASTString();
       ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
       myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
       for(String mysublen:myAllAssuSubLens){
         mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
         subToLenNums.add(Pair.of(mysublen,arrLen ));
       }
       break;
     case StatementEdge:
       CStatementEdge statementEdge=(CStatementEdge)edge;
       CStatement expression=statementEdge.getStatement();
       if(expression instanceof CAssignment){
         CAssignment assignmentExp=(CAssignment)expression;
         CExpression op1=assignmentExp.getLeftHandSide();
        CRightHandSide op2=  assignmentExp.getRightHandSide();
        String op2str=op2.toASTString();
        String op1str=op1.toASTString();
        String str=op1str+"="+op2str;
        if(op1 instanceof CUnaryExpression){//======================================================左边是*(a+1)形式
          UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();

          switch(unaryOperator){
          case STAR:
            if(((CUnaryExpression) op1).getOperand() instanceof CBinaryExpression){
            CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
          BinaryOperator starOperator=  unaryOperand.getOperator();
          switch(starOperator){
          case PLUS:
          String  subVal=  unaryOperand.getOperand2().toASTString();
          arrLen= CRLGlobal.getInstance().getPointerArrFullLen();

         /* arrSubVal="("+tempArrSubVal+")+"+"("+subVal+")";//得到数组下标，用p临时值加上*(p+1)后面的1
          subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
          ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
          myAllSubLens=getAllArrLens(str,arrName);
          for(String mysublen:myAllSubLens){
            mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }
          }

          }//二元操作结束
            else if(((CUnaryExpression) op1).getOperand() instanceof CIdExpression){
              //CIdExpression unaryOperand=(CIdExpression) ((CUnaryExpression) op1).getOperand();
              /*arrSubVal="("+tempArrSubVal+")";
             arrLen= CRLGlobal.getInstance().getPointerArrFullLen();
              subToLenNums.add(Pair.of(arrSubVal,arrLen));*/
              ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
              myAllSubLens=getAllArrLens(str,arrName);
              for(String mysublen:myAllSubLens){
                mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
                subToLenNums.add(Pair.of(mysublen,arrLen ));
              }


            }
          }
         }//if结束，左边是*()形式结束
        else{
          //注意此处等有*多提取方法再做处理=============================================多方法再处理=====记得注意啊
          ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
          myAllSubLens=getAllArrLens(str,arrName);
          for(String mysublen:myAllSubLens){
            mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }
        }
        }
       break;

     }

    } else if(funStrLen.equals("two_array")){
      List<Pair<String,String>> subtwolens=CFAUtils.subTwoLens;
      Map<String,Pair<String,String>> fulltwolens=CPAchecker.twoLens;
      for(Map.Entry<String,Pair<String,String>> entry:fulltwolens.entrySet()){//遍历map找到fulllength两个
        String key=entry.getKey();
        Pair<String,String> fullvals=entry.getValue();

        if(key.equals(funnameToArrname)){
         String firstfullval= fullvals.getFirst();//得到第一个fulllen
         String secondfullval=fullvals.getSecond();//得到第二个fulllen
         for(Pair<String,String> mysubtwolen:subtwolens){
           String firstsublen=mysubtwolen.getFirst();
           String secondsublen=mysubtwolen.getSecond();
           subToLenNums.add(Pair.of(firstsublen, firstfullval));
           subToLenNums.add(Pair.of(secondsublen, secondfullval));
         }
        }
      }
    }
    //不是通过functionCallEdge得到的=========================1
    else{
      arrLen=funStrLen;   //得到数组长度
      switch(edge.getEdgeType()){
      case AssumeEdge://待解决
        CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
        CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
        String assumeedgestr= binaryExp.toASTString();
        ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
        myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
        for(String mysublen:myAllAssuSubLens){
          subToLenNums.add(Pair.of(mysublen,arrLen ));
        }
      break;


      case StatementEdge://得到数组下标
        CStatementEdge statementEdge=(CStatementEdge)edge;
        CStatement expression=statementEdge.getStatement();
        if(expression instanceof CAssignment){
          CAssignment assignmentExp=(CAssignment)expression;
          CExpression op1=assignmentExp.getLeftHandSide();
         CRightHandSide op2=  assignmentExp.getRightHandSide();
         String op2str=op2.toASTString();
         String op1str=op1.toASTString();
         String str=op1str+"="+op2str;
          if(op1 instanceof CArraySubscriptExpression){//===================================================左边是a[]形式
           // CIdExpression arrSubExp=(CIdExpression)((CArraySubscriptExpression) op1).getArrayExpression();
             //arrSubVal=((CArraySubscriptExpression) op1).getSubscriptExpression().toASTString();
             //subToLenNums.add(Pair.of(arrSubVal,arrLen ));
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
             myAllSubLens=getAllArrLens(str,arrName);
             for(String mysublen:myAllSubLens){
               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }



          }else if(op1 instanceof CUnaryExpression){//======================================================左边是*(a+1)形式
            UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();

            switch(unaryOperator){
            case STAR:
              CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
            BinaryOperator starOperator=  unaryOperand.getOperator();
            switch(starOperator){
            case PLUS:
            /*String  subVal=  unaryOperand.getOperand2().toASTString();
            arrSubVal="("+subVal+")";
            subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
            ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
            myAllSubLens=getAllArrLens(str,arrName);
            for(String mysublen:myAllSubLens){
              subToLenNums.add(Pair.of(mysublen,arrLen ));
            }
            }

            }
           }else{//=====================================================================================左边不是上面的两种形式
             //记得改回来
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
             myAllSubLens=getAllArrLens(op2str,arrName);
             for(String mysublen:myAllSubLens){
               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }

           }


        }
        break;

      default:
       String str= edge.getRawStatement();
       ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
       myAllSubLens=getAllArrLens(str,arrName);
       for(String mysublen:myAllSubLens){
         subToLenNums.add(Pair.of(mysublen,arrLen ));
       }
       break;
      }

      }


    //龙结束==========================================================================================================龙得到subs和名字和长度结束


    //得到四个d，!d,r,！r
    System.out.println(subToLenNums);

    List<Pair<String,String>> savelist=new ArrayList<Pair<String,String>>(props.keySet());

    String global="";
    if(proposition.getGlobalVar().size()!=0){
      for(String s: proposition.getGlobalVar()){
        global=global+"int "+s+";\n";
      }
    }

    //对四个命题进行处理===================================
    //用statements[0]存r与d，用statements[1]存!r!d=====让r与d结合，!r和!d结合=======[blkNum!=0&&blkNum==blkNum&&, !(blkNum==blkNum)&&!(blkNum!=0)&&]





    for(Pair<String,String> mypl:subToLenNums){//为实现多边一起加入而加入的for循环==============================多边
      List<Pair<String,String>> list=new ArrayList<Pair<String,String>>(savelist);
      String[] statements={"",""};

    for(int i=0;i<list.size();i++){
      //龙测试
      Pair<String,String> pl=list.get(i);
      String firstT=pl.getFirst();//第一个：!r====第二个：r=====第三个：d

      if(pl.getFirst().equals("al")||pl.getFirst().equals("!al")){

        String secondT=pl.getSecond();

            if((secondT!=null)&&(arrName!=null)&&(mypl.getFirst()!=null)&&(mypl.getSecond()!=null)){


                 String   temparrname=arrName.replaceAll("\\*", "\\\\*");
                 temparrname=temparrname.replaceAll("\\.", "\\\\.");
              secondT=secondT.replaceFirst(temparrname,mypl.getFirst());
               secondT=secondT.replaceAll("length",mypl.getSecond());

         }
       pl=Pair.of(firstT,secondT);
       list.set(i, pl);
      }
      //龙测试结束

      if(!pl.getFirst().startsWith("!"))
       statements[0]=statements[0]+pl.getSecond()+"&&";
      else
       statements[1]=statements[1]+pl.getSecond()+"&&";
    }

    Map<Pair<String,String>,CFAEdge> pEdges=new HashMap<Pair<String,String>,CFAEdge>();

    for(int i=0;i<2;i++){
      String statement=statements[i];
      statement=statement.substring(0,statement.lastIndexOf("&&")).trim();
      String[] ss=statement.split("&&");//i=0时ss得到[blkNum!=0, blkNum==blkNum]
      for(int j=0;j<ss.length;j++){
      statement=ss[j];

      String statement1="int main(){if("+statement+");}";
      ParseResult myString=parser.parseString(global+statement1);
      Map<String, FunctionEntryNode> fn=myString.getFunctions();
      CFANode node=fn.get("main");
      while(node.getNumLeavingEdges()!=0){
        if(node.getNumLeavingEdges()==1){
          node=node.getLeavingEdge(0).getSuccessor();
          continue;
        }
        List<CFAEdge> edges=node.getLeavingEdge();
        boolean tb=false;
        for(CFAEdge e:edges){
          for(Pair<String,String> p:list)
           if(e.getRawStatement().equals("["+statement+"]")&&statement.equals(p.getSecond())){
             if(statement.contains("==")){
               String s[]=statement.split("==");
               if(s[0].startsWith("!(")){
                 s[0]=s[0].substring(2);
                 s[1]=s[1].substring(0,s[1].length()-1);
               }
               if(!(s.length==2&&s[0].equals(s[1]))){
                 pEdges.put(p, e);
               }
             }
             else{
              pEdges.put(p, e);
             }
            tb=true;
            node=e.getSuccessor();
            break;
          }
          if(tb){
            break;
          }
        }
      }
     }
    }
dNotDEdges.add(pEdges);

    }//加入的for循环结束


return dNotDEdges;
}
  public static ArrayList<String> getAllArrLens(String str,String arrayName){

    Stack<Character>  stack=new Stack<Character>();
    Map<Integer,Integer> map=new HashMap<Integer,Integer>();
    ArrayList<String>  myAllSubs=new ArrayList<String>();
    List<Integer>  templeft=new ArrayList<Integer>();//储存'['的在字符串中位置
    List<Integer>  templeft1=new ArrayList<Integer>();//储存'('的在字符串中位置
    stack.push('A');
        str=str.replaceAll(" ", "");
        if(arrayName.contains(".")){
          arrayName=arrayName.replaceAll(arrayName, "("+arrayName+")");
          arrayName=arrayName.replaceAll("\\(","\\\\(");
          arrayName=arrayName.replaceAll("\\)","\\\\)");
          arrayName=arrayName.replaceAll("\\[","\\\\[");
          arrayName=arrayName.replaceAll("\\]","\\\\]");


          str=str.replaceAll(arrayName, "#");
          }else{ str=str.replaceAll(arrayName, "#");}
        if(str.contains("*#")){
          str=str.replaceAll("\\*\\#", "\\$");
        }
        if(str.contains("*(#)")){
           str= str.replaceAll("\\*\\(\\#\\)", "\\$");
        }
       char[] arr=str.toCharArray();


       for(int k=0;k<arr.length;k++){
         char c=arr[k];
         Character temp =stack.pop();
         if(c=='$'){
           myAllSubs.add("0");
         }
         if(temp=='A'){
           stack.push(temp);
         }



         if (temp == '[' && c == ']') { // ===============================总1

  if((templeft.get(templeft.size()-1)-3)>=0){
    if((arr[templeft.get(templeft.size()-1)-1]=='#')||((arr[templeft.get(templeft.size()-1)-1]==')')&&(arr[templeft.get(templeft.size()-1)-2]=='#')&&(arr[templeft.get(templeft.size()-1)-3]=='('))){

      map.put(templeft.get(templeft.size()-1), k);
      templeft.remove(templeft.size()-1);

      }
  }else{
    if((arr[templeft.get(templeft.size()-1)-1]=='#')){
      map.put(templeft.get(templeft.size()-1), k);
      templeft.remove(templeft.size()-1);
    }
  }





        }else if(temp == '(' && c == ')'){
          if(templeft1.get(templeft1.size()-1)>=1){//考虑 ()左括号前面没东西
            //System.out.println(arr[templeft1.get(templeft1.size()-1)-1]);
            //System.out.println(arr[templeft1.get(templeft1.size()-1)+1]);
          if((arr[templeft1.get(templeft1.size()-1)-1]=='*')&&(arr[templeft1.get(templeft1.size()-1)+1]=='#')){

             map.put(templeft1.get(templeft1.size()-1)+2, k);

             }
             templeft1.remove(templeft1.size()-1);
          }

        }else if(temp=='['||temp=='(')
          stack.push(temp);
         if (c == '[') {
             stack.push(c);
             templeft.add(k);



           } if(c=='('){
             stack.push(c);
             templeft1.add(k);
           }



        }
       for(Map.Entry<Integer,Integer> entry:map.entrySet()){
         int i=entry.getKey();
         int j=entry.getValue();
         String sunstr="("+(String) str.subSequence(i+1, j)+")";

         myAllSubs.add(sunstr);


       }
   return myAllSubs;
  }

  public void propositionToCFAEdgeForPointer(LogManager logger,Configuration config,Proposition proposition) throws InvalidConfigurationException, ParserException{
     parser=CParser.Factory.getParser(logger, CParser.Factory.getOptions(config));
     Map<Pair<String, String>, String> props = proposition.getPropositions();
     List<Pair<String, String>> list = new ArrayList<Pair<String, String>>(props.keySet());
     String global = "";
     if (proposition.getGlobalVar().size() != 0) {
       for (String s : proposition.getGlobalVar()) {
         global = global + "int " + s + ";\n";
       }
     }
     String[] statements = { "", "" };
     for (Pair<String, String> pl : list) {
       if (!pl.getFirst().startsWith("!"))
         statements[0] = statements[0] + pl.getSecond() + "&&";
       else
         statements[1] = statements[1] + pl.getSecond() + "&&";
     }
     Map<Pair<String, String>, CFAEdge> pEdges = new HashMap<Pair<String, String>, CFAEdge>();

     for (int i = 0; i < 2; i++) {
       String statement = statements[i];
       statement = statement.substring(0, statement.lastIndexOf("&&")).trim();
       String[] ss = statement.split("&&");
       for (int j = 0; j < ss.length; j++) {
         statement = ss[j];

         String statement1 = "int main(){if(" + statement + ");}";
         ParseResult myString = parser.parseString(global + statement1);
         Map<String, FunctionEntryNode> fn = myString.getFunctions();
         CFANode node = fn.get("main");
         while (node.getNumLeavingEdges() != 0) {
           if (node.getNumLeavingEdges() == 1) {
             node = node.getLeavingEdge(0).getSuccessor();
             continue;
           }
           List<CFAEdge> edges = node.getLeavingEdge();
           boolean tb = false;
           for (CFAEdge e : edges) {
             for (Pair<String, String> p : list)
               if (e.getRawStatement().equals("[" + statement + "]") && statement.equals(p.getSecond())) {
                 if (statement.contains("==")) {
                   String s[] = statement.split("==");
                   if (s[0].startsWith("!(")) {
                     s[0] = s[0].substring(2);
                     s[1] = s[1].substring(0, s[1].length() - 1);
                   }
                   if (!(s.length == 2 && s[0].equals(s[1]))) {
                     pEdges.put(p, e);
                   }
                 }
                 else {
                   pEdges.put(p, e);
                 }
                 tb = true;
                 node = e.getSuccessor();
                 break;
               }
             if (tb) {
               break;
             }
           }
         }
       }
     }
     proposition.setPropEdges(pEdges);
   }
  public void propositionToCFAEdgeForArray(LogManager logger,Configuration config,Proposition proposition) throws InvalidConfigurationException, ParserException{
    parser=CParser.Factory.getParser(logger, CParser.Factory.getOptions(config));
    Map<Pair<String, String>, String> props = proposition.getPropositions();
    List<Pair<String, String>> list = new ArrayList<Pair<String, String>>(props.keySet());
    String global = "";
    if (proposition.getGlobalVar().size() != 0) {
      for (String s : proposition.getGlobalVar()) {
        global = global + "int " + s + ";\n";
      }
    }
    String[] statements = { "", "" };
    for (Pair<String, String> pl : list) {
      if (!pl.getFirst().startsWith("!"))
        statements[0] = statements[0] + pl.getSecond() + "&&";
      else
        statements[1] = statements[1] + pl.getSecond() + "&&";
    }
    Map<Pair<String, String>, CFAEdge> pEdges = new HashMap<Pair<String, String>, CFAEdge>();

    for (int i = 0; i < 2; i++) {
      String statement = statements[i];
      statement = statement.substring(0, statement.lastIndexOf("&&")).trim();
      String[] ss = statement.split("&&");
      for (int j = 0; j < ss.length; j++) {
        statement = ss[j];

        String statement1 = "int main(){if(" + statement + ");}";
        ParseResult myString = parser.parseString(global + statement1);
        Map<String, FunctionEntryNode> fn = myString.getFunctions();
        CFANode node = fn.get("main");
        while (node.getNumLeavingEdges() != 0) {
          if (node.getNumLeavingEdges() == 1) {
            node = node.getLeavingEdge(0).getSuccessor();
            continue;
          }
          List<CFAEdge> edges = node.getLeavingEdge();
          boolean tb = false;
          for (CFAEdge e : edges) {
            for (Pair<String, String> p : list)
              if (e.getRawStatement().equals("[" + statement + "]") && statement.equals(p.getSecond())) {
                if (statement.contains("==")) {
                  String s[] = statement.split("==");
                  if (s[0].startsWith("!(")) {
                    s[0] = s[0].substring(2);
                    s[1] = s[1].substring(0, s[1].length() - 1);
                  }
                  if (!(s.length == 2 && s[0].equals(s[1]))) {
                    pEdges.put(p, e);
                  }
                }
                else {
                  pEdges.put(p, e);
                }
                tb = true;
                node = e.getSuccessor();
                break;
              }
            if (tb) {
              break;
            }
          }
        }
      }
    }
    proposition.setPropEdges(pEdges);
  }
   public void propositionToCFAEdgeForSimpleProperty(LogManager logger,Configuration config,Proposition proposition) throws InvalidConfigurationException, ParserException{
     parser=CParser.Factory.getParser(logger, CParser.Factory.getOptions(config));
     Map<Pair<String, String>, String> props = proposition.getPropositions();
     List<Pair<String, String>> list = new ArrayList<Pair<String, String>>(props.keySet());
     String global = "";
     if (proposition.getGlobalVar().size() != 0) {
       for (String s : proposition.getGlobalVar()) {
         global = global + "int " + s + ";\n";
       }
     }
     String[] statements = { "", "" };
     for (Pair<String, String> pl : list) {
       if (!pl.getFirst().startsWith("!"))
         statements[0] = statements[0] + pl.getSecond() + "&&";
       else
         statements[1] = statements[1] + pl.getSecond() + "&&";
     }
     Map<Pair<String, String>, CFAEdge> pEdges = new HashMap<Pair<String, String>, CFAEdge>();

     for (int i = 0; i < 2; i++) {
       String statement = statements[i];
       statement = statement.substring(0, statement.lastIndexOf("&&")).trim();
       String[] ss = statement.split("&&");
       for (int j = 0; j < ss.length; j++) {
         statement = ss[j];

         String statement1 = "int main(){if(" + statement + ");}";
         ParseResult myString = parser.parseString(global +statement1);
         Map<String, FunctionEntryNode> fn = myString.getFunctions();
         CFANode node = fn.get("main");
         while (node.getNumLeavingEdges() != 0) {
           if (node.getNumLeavingEdges() == 1) {
             node = node.getLeavingEdge(0).getSuccessor();
             continue;
           }
           List<CFAEdge> edges = node.getLeavingEdge();
           boolean tb = false;
           for (CFAEdge e : edges) {
             for (Pair<String, String> p : list)
               if (e.getRawStatement().equals("[" + statement + "]") && statement.equals(p.getSecond())) {
                 if (statement.contains("==")) {
                   String s[] = statement.split("==");
                   if (s[0].startsWith("!(")) {
                     s[0] = s[0].substring(2);
                     s[1] = s[1].substring(0, s[1].length() - 1);
                   }
                   if (!(s.length == 2 && s[0].equals(s[1]))) {
                     pEdges.put(p, e);
                   }
                 }
                 else {
                   pEdges.put(p, e);
                 }
                 tb = true;
                 node = e.getSuccessor();
                 break;
               }
             if (tb) {
               break;
             }
           }
         }
       }
     }
     proposition.setPropEdges(pEdges);
   }
   public void extractPropositions(CFA cfa) {
     // TODO Auto-generated method stub

     // TODO Auto-generated method stub
     Iterator<CFANode> iterator=cfa.getAllNodes().iterator();
     int j=1;
     while(iterator.hasNext()){
       CFANode next=iterator.next();
       if(next instanceof CFunctionEntryNode){
         String f=next.getFunctionName();
         List<CParameterDeclaration> ptmp=((CFunctionEntryNode) next).getFunctionParameters();
         List<String> paras=new ArrayList<String>();
         for(CParameterDeclaration p:ptmp){
           paras.add(p.getName());
           CType type=p.getType();
           String typename="basicType";
           if(type instanceof CPointerType ){
             if(((CPointerType) type).getType() instanceof CNamedType)
              typename=((CNamedType) ((CPointerType) type).getType()).getName();
             else if(((CPointerType) type).getType() instanceof CElaboratedType){
               typename=((CElaboratedType) ((CPointerType) type).getType()).getName();
             }
           }

           GlobalInfo.getInstance().addVarToType(f+"::"+p.getName(), typename);
         }
         GlobalInfo.getInstance().addFunction(f, paras);
       }
       List<CFAEdge> edges=next.getLeavingEdge();
       for(CFAEdge edge:edges){
         String func=edge.getPredecessor().getFunctionName();
         if(edge instanceof CFunctionCallEdge){
          List<Integer> types=new ArrayList<Integer>();
          List<String>  vars=new ArrayList<String>();
          List<CExpression> fc=((CFunctionCallEdge)(edge)).getArguments();
          for(CExpression e:fc){
            CType type=e.getExpressionType();
            if(type instanceof CPointerType)
               types.add(1);
            else
               types.add(0);
          }
          CFANode suc=edge.getSuccessor();
          if(suc instanceof CFunctionEntryNode){
            vars=((CFunctionEntryNode) suc).getFunctionParameterNames();
          }
          for(int i=0;i<types.size()&&vars.size()==types.size();i++){
            if(types.get(i)==1){
              String function=suc.getFunctionName();
              String var=function+"::"+vars.get(i);
              String first="d=>"+var+" != 0";
              String second="r=>"+var+" == "+var;
              propositionsMap.put(var,Pair.of(first, second));
            }
          }
         }
         else if(edge instanceof CDeclarationEdge){
           CDeclaration declaration=((CDeclarationEdge) edge).getDeclaration();
           if(declaration instanceof CVariableDeclaration){
             ((CDeclarationEdge) edge).setDo(true);
             String function="";
             String var=declaration.getName();
             CType type=declaration.getType();

             if(declaration.isGlobal()){
               function="Global";
             }
             else{
               function=next.getFunctionName();
             }
             if(type instanceof CPointerType){
               String typename="basicType";
               if(((CPointerType) type).getType() instanceof CNamedType){
                 CNamedType type1= (CNamedType) ((CPointerType) type).getType();
                 typename = type1.getName();
               }
               else if(((CPointerType) type).getType() instanceof CElaboratedType){
                 CElaboratedType type1= (CElaboratedType) ((CPointerType) type).getType();
                 typename = type1.getName();
               }
               GlobalInfo.getInstance().addVarToType(function+"::"+var, typename);
               var=function+"::"+var;
               String first="d=>"+var+" != 0";
               String second="r=>"+var+" == "+var;
               propositionsMap.put(var,Pair.of(first, second));

             }
           }
           else if(declaration instanceof CTypeDefDeclaration||declaration instanceof CComplexTypeDeclaration){
               CType type=declaration.getType();
               Map<String,String> mem=new HashMap<String,String>();
               if(type instanceof CCompositeType){
                 String name =((CCompositeType) type).getName();
                 List<CCompositeTypeMemberDeclaration> members=((CCompositeType) type).getMembers();
                 for(CCompositeTypeMemberDeclaration member:members){
                   CType memberType=member.getType();
                   if( memberType instanceof CPointerType){
                     String typename="basicType";
                     if(((CPointerType) memberType).getType() instanceof CNamedType){
                       typename=((CNamedType) ((CPointerType) memberType).getType()).getName();
                     }
                     mem.put(member.getName(), typename);
                   }
                 }
                 if(mem.size()!=0){
                   GlobalInfo.getInstance().addStructType(name,mem);
                   GlobalInfo.getInstance().addStructSize(name,mem.size());
                 }
               }
               else if(type instanceof CNamedType){
                 String typename=((CNamedType) type).getName();
                 String orgname=declaration.getName();
                 Map<String,String> mem1=GlobalInfo.getInstance().getStructType().get(orgname);
                 GlobalInfo.getInstance().addStructType(typename,mem1);
                 GlobalInfo.getInstance().addStructSize(typename,mem.size());
               }
           }
         }
       }
     }
     GlobalInfo.getInstance().printImportantVars();

   }
  public void extractPropositionsForArray(CFA cfa) {
    // TODO Auto-generated method stub
    propositionsMap=new HashMap<String,Pair<String,String>>();//保存所有命题
    CPAchecker.nameToLen=new HashMap<String,String>();
   Map<String,String> temp_nameToLen=new HashMap<String,String>();
   CPAchecker.twoLens=new HashMap<String,Pair<String,String>>();
    CPAchecker.pureNameLen=new HashMap<String,String>();//记录普通数组名字和长度


    Map<String,String> long_nameToLen=new HashMap<String,String>();//暂时记录加入的指向数组的指针
    CPAchecker.long_firstNameToPureLen=new HashMap<String,String>();//记录指针和第一次初始长度==
    Map<String,String>  long_tempNameToPureLen=new HashMap<String,String>();//记录指针和初始长度==例如p=a;p=b;q=p,第一次记录<p,a.len>,第二次记录<p,b.len>,第三次记录<q,b.len>

    //结构体两个结构
    Map<Pair<String,String>,Pair<String,String>> tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();//记录定义结构<student1::a,length>
    Map<String,String> lastnameTOarrlen=new HashMap<String,String>();//记录声明语句结构：<std.a,length> <std.std1.a,lenth>

    List<CFAEdge> funcalledges=new ArrayList<CFAEdge>();

       //extractPropositions(cfa,propositionsMap);//==============================================消除dz==1

       //=====提取数组相应length长度==========================================================================龙开始======

       //龙开发代码===============记录所有数组=========================
     //  Map<String,BigInteger> arrNameLen=new HashMap<String,BigInteger>();
       for(CFANode node:cfa.getAllNodes()){
        // System.out.println(nameToLen);
         for(int edgeIdx=0;edgeIdx<node.getNumLeavingEdges();edgeIdx++){
           CFAEdge edge=node.getLeavingEdge(edgeIdx);
          // System.out.println(edge.toString());
          switch(edge.getEdgeType()){
          //===============================================================================================1.指针
          case StatementEdge:

            CStatementEdge statementEdge=(CStatementEdge)edge;
            CStatement expression= statementEdge.getStatement();
            if(expression instanceof CAssignment){
              CAssignment assignmentExpression=(CAssignment)expression;
              CExpression op1=assignmentExpression.getLeftHandSide();
              CRightHandSide op2= assignmentExpression.getRightHandSide();
              if(op1 instanceof CIdExpression){
               CIdExpression op1IdExp=(CIdExpression)op1;
               String op1PointerName= op1IdExp.getName();
               String op1funcname=node.getFunctionName();
               String op1fullname=op1funcname+"::"+op1PointerName;
               boolean funparaarr=false;
               if(CPAchecker.nameToLen.containsKey(op1fullname)){
                 if(CPAchecker.nameToLen.get(op1fullname).equals("function_parameter_array")){
                   funparaarr=true;
                 }
               }
               if((op1IdExp.getExpressionType() instanceof CPointerType)&&(!funparaarr)){//op1是指针形式

                 //System.out.println(op2.getExpressionType());
                 if((op2.getExpressionType() instanceof CPointerType)&&(op2 instanceof CIdExpression)){//1.op2也是指针形式q=p形式===================注意：考虑p=q+1或p=q-1等此处没有考虑================注意啊


                   CIdExpression op2IdExp=(CIdExpression)op2;
                   String arrName=op2IdExp.getName();
                   Set<String> pointernameKeys=long_tempNameToPureLen.keySet();
                   for(String pointernameKey:pointernameKeys){

                     int a=pointernameKey.indexOf("::");
                    String pointernameKey1=pointernameKey.substring(a+2).trim();
                     if(pointernameKey1.trim().equals(arrName.trim())){//例如q=p表示 temp中有p，当前p指向数组,arrName是op2name

                       Set<String> myFirstPureLenToNames=CPAchecker.long_firstNameToPureLen.keySet();
                       String  function=node.getFunctionName();//注意处理global情形======注意
                       //}

                       arrName=op1IdExp.getName();
                      String exArrName=function+"::"+arrName;//记录op1中q全名


                       String myTempPointerLen =long_tempNameToPureLen.get(pointernameKey);//记录数组长度，指针指向===如q=p,找到p指针的数组长度

                       if(!myFirstPureLenToNames.contains(exArrName)){
                         String arrNameop1=op1IdExp.getName();
                         String exArrNameop1=function+"::"+arrNameop1;
                          String first="al=>"+exArrNameop1+" < length";
                          String second="au=>"+exArrNameop1+" == "+exArrNameop1;
                          propositionsMap.put(exArrNameop1,Pair.of(first, second));
                          long_tempNameToPureLen.put(exArrNameop1, myTempPointerLen);
                          CPAchecker.long_firstNameToPureLen.put(exArrNameop1, myTempPointerLen);

                       }else{
                         String arrNameop1=op1IdExp.getName();
                         String exArrNameop1=function+"::"+arrNameop1;
                          String first="al=>"+exArrNameop1+" < length";
                          String second="au=>"+exArrNameop1+" == "+exArrNameop1;
                          propositionsMap.put(exArrNameop1,Pair.of(first, second));
                          long_tempNameToPureLen.put(exArrNameop1, myTempPointerLen);
                       }




                       }

                     }



                 }//右边是指针的形式结束
                 else{
                  String op2Str= op2.toASTString();
                  boolean myflag=false;//表示是否是a+huo+a此种形式
                  String op2StrNoSpace=op2Str.replaceAll(" ", "");
                  Set<String> nameKeys=CPAchecker.nameToLen.keySet();
                  String function=node.getFunctionName();
                  String op2name=function+"::"+op2Str;
                  String tempA = null;
                  for(String nameKey:nameKeys){
                    int a=nameKey.indexOf("::");
                    String nameKeyPure=nameKey.substring(a+2).trim();
                    if(op2StrNoSpace.matches(nameKeyPure.trim()+"\\+.*")||op2StrNoSpace.matches(".*\\+"+nameKeyPure.trim())){
                       tempA =nameKeyPure;
                      myflag=true;

                    }

                  }
                    if(nameKeys.contains(op2name)){//第一中情形：a数组名，加入p
                     /* if(statementEdge.getStatement().){
                        function="Global";
                      }else{*/

                      //}
                      String arrName=op1IdExp.getName();

                     String exArrName=function+"::"+arrName;

                     String myTempPointerLen =CPAchecker.nameToLen.get(op2name);//记录数组长度，指针指向===如p=a,找到a数组长度
                      String first="al=>"+exArrName+" < length";

                      String second="au=>"+exArrName+" == "+exArrName;
                      propositionsMap.put(exArrName,Pair.of(first, second));
                   //   long_nameToLen.put(exArrName, "pointer_array");

                     Set<String> myTempPureLenToNames=long_tempNameToPureLen.keySet();

                      if(long_tempNameToPureLen.isEmpty()){
                        long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                        CPAchecker.long_firstNameToPureLen.put(exArrName, myTempPointerLen);//注意，第一个肯定是指针指向数组
                      }
                      else if(!(myTempPureLenToNames.contains(exArrName))){
                        CPAchecker.long_firstNameToPureLen.put(exArrName, myTempPointerLen);
                        long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                      }else{
                      long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                      }

                    }
                    else if(myflag){//第二种情形：a+或+a


                      CRLGlobal.getInstance().setPointerGloLen(op2Str.replaceAll(tempA,"0"));
                        function=node.getFunctionName();
                      String arrName=op1IdExp.getName();

                      String exArrName=function+"::"+arrName;
                      String exArrName1=function+"::"+tempA;
                      String myTempPointerLen =CPAchecker.nameToLen.get(exArrName1);//记录数组长度，指针指向===如p=a+1,找到a数组长度
                       String first="al=>"+exArrName+" < length";
                       String second="au=>"+exArrName+" == "+exArrName;
                       propositionsMap.put(exArrName,Pair.of(first, second));
                     //  long_nameToLen.put(exArrName, "pointer_array");
                       Set<String> myTenpPureLenToNames=long_tempNameToPureLen.keySet();

                       if(long_tempNameToPureLen.isEmpty()){
                         long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                         CPAchecker.long_firstNameToPureLen.put(exArrName, myTempPointerLen);//注意，第一个肯定是指针指向数组
                       }
                       if(!(myTenpPureLenToNames.contains(exArrName))){
                         CPAchecker.long_firstNameToPureLen.put(exArrName, myTempPointerLen);
                         long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                       }
                       long_tempNameToPureLen.put(exArrName, myTempPointerLen);

                    }else{//即左边是指针形式，右边不是指针，不是a，不是a+形式，得看看long_tempNameToPureLen里是否有此指针，有的话，把次记录去除
                      Set<String> myTenpPureLenToNames=long_tempNameToPureLen.keySet();
                        function=node.getFunctionName();//注意处理global情形======注意
                      //}
                      String arrName=op1IdExp.getName();

                     String exArrName=function+"::"+arrName;
                      if(myTenpPureLenToNames.contains(exArrName)){
                        long_tempNameToPureLen.remove(exArrName);                     }

                    }


                 }//else在此处结束
               }
             }


          }
            Map<String,String> temp_long_nameToLen=CPAchecker.long_firstNameToPureLen;

            for(Map.Entry<String,String> entry:temp_long_nameToLen.entrySet()){
             entry.setValue("pointer_array");
            }
            CPAchecker.nameToLen.putAll(temp_long_nameToLen);




           break;
         //================================================================================================2.方法调用
          case FunctionCallEdge:

            funcalledges.add(edge);

            break;//待解决=======================================方法调用中用到声明数组，得考虑


            //==================================================================================================3.声明语句：包括一般数组处理和结构体处理
          case DeclarationEdge:
            CDeclarationEdge declarationEdge=(CDeclarationEdge)edge;
            String function="";
            CType type=declarationEdge.getDeclaration().getType();
            if(declarationEdge.getDeclaration().isGlobal()){
              function="Global";
            }else{
              function=node.getFunctionName();
            }
            String arrName=declarationEdge.getDeclaration().getName();//struct student std；===是std
             if(type instanceof CArrayType){//=======================================================================3.1:一般数组 he 结构体数组  处理
                     CArrayType arr=(CArrayType)declarationEdge.getDeclaration().getType();
                     if(arr.getType() instanceof CArrayType){//===================简单二维数组处理
                    String  secondLenStr= arr.getLength().toASTString();
                    CArrayType arrArr=(CArrayType)arr.getType();
                    String firstLenStr=arrArr.getLength().toASTString();
                    arrName=function+"::"+arrName;
                    String first="al=>"+arrName+" < length";
                    String second="au=>"+arrName+" == "+arrName;
                    propositionsMap.put(arrName,Pair.of(first, second));
                    CPAchecker.nameToLen.put(arrName, "two_array");
                    CPAchecker.twoLens.put(arrName, Pair.of(firstLenStr, secondLenStr));

                     }else if(arr.getType() instanceof CSimpleType){//========================================================简单一维数组
                       if(arr.getLength()!=null){
                     String arrLenStr=arr.getLength().toASTString();
                     arrName=function+"::"+arrName;
                     String first="al=>"+arrName+" < length";
                     String second="au=>"+arrName+" == "+arrName;
                     propositionsMap.put(arrName,Pair.of(first, second));
                     CPAchecker.nameToLen.put(arrName, arrLenStr);
                     CPAchecker.pureNameLen.put(arrName, arrLenStr);
                       }
                     }else if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){//外部声明结构体数组：：：struct student std[2]

                       //CArrayType arrType=(CArrayType)arr.getType();
                       String name2=arrName;//得到std名字
                       int structArrLen=0;
                       if(arr.getLength() instanceof CIntegerLiteralExpression){
                          structArrLen=((CIntegerLiteralExpression)arr.getLength()).getValue().intValue();
                       }
                       if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){
                         String name1=null;
                         if(arr.getType() instanceof CElaboratedType){
                         CElaboratedType elaType=(CElaboratedType)arr.getType();
                         name1= elaType.getName();//student===类型名字
                         }else if(arr.getType() instanceof CNamedType){
                           CNamedType elaType=(CNamedType)arr.getType();
                           name1= elaType.getName();//STUDENT===类型名字
                         }
                        //看temp中是否有student，有的话则加入到nameToLen
                        if(!(tempnameTOarrlen.isEmpty())){
                          Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                          for(Pair<String,String> tempname:tempnames){
                           String first= tempname.getFirst();
                           String second=tempname.getSecond();
                           if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入std[0].a和std[1].a
                             for(int structarrlen=0;structarrlen<structArrLen;structarrlen++){
                             String structArrName="("+name2+"["+structarrlen+"])"+"."+second;
                             //String structArrName1=name2+"->"+second;
                             Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                             String firstlenstr=lens.getFirst();
                             String secondlenstr=lens.getSecond();
                             if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体数组外部声明
                             String arrLenStr= firstlenstr;

                             arrName=function+"::"+structArrName;
                             String first1="al=>"+arrName+" < length";
                             String second1="au=>"+arrName+" == "+arrName;
                             propositionsMap.put(arrName,Pair.of(first1, second1));
                             CPAchecker.nameToLen.put(arrName, arrLenStr);
                             CPAchecker.pureNameLen.put(arrName, arrLenStr);


                             }else{//========================================二维数组碰到结构体数组外部声明
                               arrName=function+"::"+structArrName;
                               String first1="al=>"+arrName+" < length";
                               String second1="au=>"+arrName+" == "+arrName;
                               propositionsMap.put(arrName,Pair.of(first1, second1));
                               CPAchecker.nameToLen.put(arrName, "two_array");
                               CPAchecker.twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                               CPAchecker.pureNameLen.put(arrName, "two_array");


                             }
                             }
                             }
                           }
                          }

                       }





                     }
             }else if(declarationEdge.getDeclaration() instanceof CComplexTypeDeclaration){//==============================3.2.1结构体 定义处理
               Map<Pair<String,String>,Pair<String,String>> temp_tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();
               CComplexTypeDeclaration comDec=(CComplexTypeDeclaration)declarationEdge.getDeclaration();
               if(comDec.getType() instanceof CCompositeType){
               CCompositeType comType=(CCompositeType)comDec.getType();
              String structName= comType.getName();//记录结构体名字，如student
              List<CCompositeTypeMemberDeclaration> listMembs=comType.getMembers();
              for(CCompositeTypeMemberDeclaration listMemb:listMembs ){
                if(listMemb.getType() instanceof CArrayType){//===================================定义中碰到数组
                 String structArrName= listMemb.getName();//记录数组名字，如a
                  CArrayType arr=(CArrayType)listMemb.getType();
                  if(arr.getType() instanceof CArrayType){//===================简单二维数组处理
                    String  secondLenStr= arr.getLength().toASTString();
                    CArrayType arrArr=(CArrayType)arr.getType();
                    String firstLenStr=arrArr.getLength().toASTString();

                    tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstLenStr, secondLenStr));

                     }else if(arr.getType() instanceof CSimpleType){//==========================================================一维数组处理
                       String structArrLen= arr.getLength().toASTString();//记录数组长度lenth
                       tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(structArrLen, "str_one_array"));


                     }else if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){//===========碰到结构体定义中内部声明： struct student1 std3[2];


                       String name2= listMemb.getName();//std1=====对象名字
                       int structArrLen=((CIntegerLiteralExpression)arr.getLength()).getValue().intValue();
                       String name1=null;
                       if(arr.getType() instanceof CElaboratedType){
                       CElaboratedType elaType=(CElaboratedType)arr.getType();
                       name1= elaType.getName();//student1===类型名字
                       }else if(arr.getType() instanceof CNamedType){
                         CNamedType elaType=(CNamedType)arr.getType();
                         name1= elaType.getName();//STUDENT1===类型名字
                       }

                      if(!(tempnameTOarrlen.isEmpty())){
                      Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                      for(Pair<String,String> tempname:tempnames){
                       String first= tempname.getFirst();
                       String second=tempname.getSecond();
                       if(first.equals(name1)){//表示有数组====存两个：temp和nameToLen 即：<student::std1.a,length>和<global::std1.a,length>
                         for(int structarrlen=0;structarrlen<structArrLen;structarrlen++){
                        // String  structfunction="Global";
                          structArrName="("+name2+"["+structarrlen+"])"+"."+second;
                         Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                         String firstlenstr=lens.getFirst();
                         String secondlenstr=lens.getSecond();
                         if(secondlenstr.equals("str_one_array")){//==========一维数组碰到内部声明
                           String arrLenStr= firstlenstr;
                           temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                           /*arrName=structfunction+"::"+structArrName;
                           String first1="d=>"+arrName+" < length";
                           String second1="r=>"+arrName+" == "+arrName;
                           propositionsMap.put(arrName,Pair.of(first1, second1));
                           nameToLen.put(arrName, arrLenStr);
                           pureNameLen.put(arrName, arrLenStr);*/
                         }else{//===========================================二维数组碰到内部声明
                           temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                           /*arrName=structfunction+"::"+structArrName;
                           String first1="d=>"+arrName+" < length";
                           String second1="r=>"+arrName+" == "+arrName;
                           propositionsMap.put(arrName,Pair.of(first1, second1));
                           nameToLen.put(arrName, "two_array");
                           twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                           pureNameLen.put(arrName, "two_array");*/
                         }

                       }
                       }
                      }

                      }


                  }
                }
                if((listMemb.getType() instanceof CElaboratedType)||(listMemb.getType() instanceof CNamedType)){//==============================定义中碰到结构体声明==内部声明

                 String name2= listMemb.getName();//std1=====对象名字
                 String name1=null;
                 if(listMemb.getType() instanceof CElaboratedType){
                 CElaboratedType elaType=(CElaboratedType)listMemb.getType();
                 name1= elaType.getName();//student1===类型名字
                 }else if(listMemb.getType() instanceof CNamedType){
                   CNamedType elaType=(CNamedType)listMemb.getType();
                   name1= elaType.getName();//STUDENT1===类型名字
                 }

                if(!(tempnameTOarrlen.isEmpty())){
                Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                for(Pair<String,String> tempname:tempnames){
                 String first= tempname.getFirst();
                 String second=tempname.getSecond();
                 if(first.equals(name1)){//表示有数组====存两个：temp和nameToLen 即：<student::std1.a,length>和<global::std1.a,length>
                   //String  structfunction="Global";
                   String structArrName=name2+"."+second;
                   Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                   String firstlenstr=lens.getFirst();
                   String secondlenstr=lens.getSecond();
                   if(secondlenstr.equals("str_one_array")){//==========一维数组碰到内部声明
                     String arrLenStr= firstlenstr;
                     temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                     /*arrName=structfunction+"::"+structArrName;
                     String first1="d=>"+arrName+" < length";
                     String second1="r=>"+arrName+" == "+arrName;
                     propositionsMap.put(arrName,Pair.of(first1, second1));
                     nameToLen.put(arrName, arrLenStr);
                     pureNameLen.put(arrName, arrLenStr);*/
                   }else{//===========================================二维数组碰到内部声明
                     temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                     /*arrName=structfunction+"::"+structArrName;
                     String first1="d=>"+arrName+" < length";
                     String second1="r=>"+arrName+" == "+arrName;
                     propositionsMap.put(arrName,Pair.of(first1, second1));
                     nameToLen.put(arrName, "two_array");
                     twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                     pureNameLen.put(arrName, "two_array");*/
                   }

                 }
                }

                }
                }else if(listMemb.getType() instanceof CPointerType){

                  CPointerType pointerType=(CPointerType)listMemb.getType();
                  if((pointerType.getType() instanceof CElaboratedType)||(pointerType.getType() instanceof CNamedType)){
                    String name2= listMemb.getName();//std1=====对象名字
                    String name1=null;
                    if(listMemb.getType() instanceof CElaboratedType){
                    CElaboratedType elaType=(CElaboratedType)listMemb.getType();
                    name1= elaType.getName();//student===类型名字
                    }else if(listMemb.getType() instanceof CNamedType){
                      CNamedType elaType=(CNamedType)listMemb.getType();
                      name1= elaType.getName();//STUDENT===类型名字
                    }
                   //看temp中是否有student，有的话则加入到nameToLen
                   if(!(tempnameTOarrlen.isEmpty())){
                     Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                     for(Pair<String,String> tempname:tempnames){
                      String first= tempname.getFirst();
                      String second=tempname.getSecond();
                      if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入两个：(*pp).a  和 pp->a
                        String structArrName="("+"*("+name2+")"+"."+second+")";
                        String structArrName1=name2+"->"+second;//==========================================================================调试
                        Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                        String firstlenstr=lens.getFirst();
                        String secondlenstr=lens.getSecond();
                        if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体指针内部声明
                        String arrLenStr= firstlenstr;
                        temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                       /* arrName=function+"::"+structArrName;
                        String first1="d=>"+arrName+" < length";
                        String second1="r=>"+arrName+" == "+arrName;
                        propositionsMap.put(arrName,Pair.of(first1, second1));
                        nameToLen.put(arrName, arrLenStr);
                        pureNameLen.put(arrName, arrLenStr);*/
                        temp_tempnameTOarrlen.put(Pair.of(structName, structArrName1), Pair.of(arrLenStr,"str_one_array"));
                        /*arrName=function+"::"+structArrName1;
                         first1="d=>"+arrName+" < length";
                        second1="r=>"+arrName+" == "+arrName;
                        propositionsMap.put(arrName,Pair.of(first1, second1));
                        nameToLen.put(arrName, arrLenStr);
                        pureNameLen.put(arrName, arrLenStr);*/
                        }else{//========================================二维数组碰到结构体指针内部声明
                          temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                          /*arrName=function+"::"+structArrName;
                          String first1="d=>"+arrName+" < length";
                          String second1="r=>"+arrName+" == "+arrName;
                          propositionsMap.put(arrName,Pair.of(first1, second1));
                          nameToLen.put(arrName, "two_array");
                          twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                          pureNameLen.put(arrName, "two_array");*/
                          temp_tempnameTOarrlen.put(Pair.of(structName, structArrName1), Pair.of(firstlenstr, secondlenstr));
                         /* arrName=function+"::"+structArrName1;
                          first1="d=>"+arrName+" < length";
                         second1="r=>"+arrName+" == "+arrName;
                         propositionsMap.put(arrName,Pair.of(first1, second1));
                          nameToLen.put(arrName, "two_array");
                          twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                          pureNameLen.put(arrName, "two_array");*/
                        }
                        }
                      }
                     }

                  }
                }

              }
             }
              tempnameTOarrlen.putAll(temp_tempnameTOarrlen);

             }else if(declarationEdge.getDeclaration() instanceof CTypeDefDeclaration){//处理typedef定义问题外部定义=======把student变成STUDENT
               Map<Pair<String,String>,Pair<String,String>> temp_tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();
               List<Pair<String,String>> temp_removepa=new ArrayList<Pair<String,String>>();
               CTypeDefDeclaration typedefDec=(CTypeDefDeclaration)declarationEdge.getDeclaration();
              String name2= typedefDec.getName();
              if(typedefDec.getType() instanceof CElaboratedType){
                CElaboratedType elaType=(CElaboratedType)typedefDec.getType();
               String name1= elaType.getName();
               if(!(tempnameTOarrlen.isEmpty())){
                 Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                 for(Pair<String,String> tempname:tempnames){
                  String first= tempname.getFirst();
                  String second=tempname.getSecond();
                  if(first.equals(name1)){
                    Pair<String,String> lens=tempnameTOarrlen.get(tempname);

                    temp_tempnameTOarrlen.put(Pair.of(name2, second), lens);
                    temp_removepa.add(tempname);

                  }
                 }
                 tempnameTOarrlen.putAll(temp_tempnameTOarrlen);
                 for(Pair<String,String> removpair:temp_removepa){
                   tempnameTOarrlen.remove(removpair);
                 }
                 }
              }



             }else if(declarationEdge.getDeclaration() instanceof CVariableDeclaration){//====================================3.2.2结构体 外面声明处理
               CVariableDeclaration  variDec=(CVariableDeclaration)declarationEdge.getDeclaration();
              String name2= variDec.getName();//std===如果是指针则是pp======对象名字=====================================下面都要用到name2
               if((variDec.getType() instanceof CElaboratedType)||(variDec.getType() instanceof CNamedType)){//=============================struct student std;
                 String name1=null;
                 if(variDec.getType() instanceof CElaboratedType){
                 CElaboratedType elaType=(CElaboratedType)variDec.getType();
                 name1= elaType.getName();//student===类型名字
                 }else if(variDec.getType() instanceof CNamedType){
                   CNamedType elaType=(CNamedType)variDec.getType();
                   name1= elaType.getName();//STUDENT===类型名字
                 }
                if(!(tempnameTOarrlen.isEmpty())){
                Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                for(Pair<String,String> tempname:tempnames){
                 String first= tempname.getFirst();
                 String second=tempname.getSecond();
                 if(first.equals(name1)){

                   String structArrName=name2+"."+second;
                   Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                   String firstlenstr=lens.getFirst();
                   String secondlenstr=lens.getSecond();
                   if(secondlenstr.equals("str_one_array")){

                   String arrLenStr= firstlenstr;

                   arrName=function+"::"+structArrName;
                   String first1="al=>"+arrName+" < length";
                   String second1="au=>"+arrName+" == "+arrName;
                   propositionsMap.put(arrName,Pair.of(first1, second1));
                   CPAchecker.nameToLen.put(arrName, arrLenStr);
                   CPAchecker.pureNameLen.put(arrName, arrLenStr);
                   }else{
                     arrName=function+"::"+structArrName;
                     String first1="al=>"+arrName+" < length";
                     String second1="au=>"+arrName+" == "+arrName;
                     propositionsMap.put(arrName,Pair.of(first1, second1));
                     CPAchecker.nameToLen.put(arrName, "two_array");
                     CPAchecker.twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                     CPAchecker.pureNameLen.put(arrName, "two_array");
                   }

                 }
                }
                }
               }

               if(variDec.getType() instanceof CPointerType){
                 CPointerType pointerType=(CPointerType)variDec.getType();
                 if((pointerType.getType() instanceof CElaboratedType)||(pointerType.getType() instanceof CNamedType)){
                   String name1=null;
                   if(pointerType.getType() instanceof CElaboratedType){
                   CElaboratedType elaType=(CElaboratedType)pointerType.getType();
                   name1= elaType.getName();//student===类型名字
                   }else if(pointerType.getType() instanceof CNamedType){
                     CNamedType elaType=(CNamedType)pointerType.getType();
                     name1= elaType.getName();//STUDENT===类型名字
                   }
                  //看temp中是否有student，有的话则加入到nameToLen
                  if(!(tempnameTOarrlen.isEmpty())){
                    Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                    for(Pair<String,String> tempname:tempnames){
                     String first= tempname.getFirst();
                     String second=tempname.getSecond();
                     if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入两个：(*pp).a  和 pp->a
                       String structArrName="(*"+name2+")"+"."+second;
                       String structArrName1=name2+"->"+second;
                       Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                       String firstlenstr=lens.getFirst();
                       String secondlenstr=lens.getSecond();
                       if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体指针外部声明
                       String arrLenStr= firstlenstr;

                       arrName=function+"::"+structArrName;
                       String first1="al=>"+arrName+" < length";
                       String second1="au=>"+arrName+" == "+arrName;
                       propositionsMap.put(arrName,Pair.of(first1, second1));
                       CPAchecker.nameToLen.put(arrName, arrLenStr);
                       CPAchecker.pureNameLen.put(arrName, arrLenStr);

                       arrName=function+"::"+structArrName1;
                        first1="al=>"+arrName+" < length";
                       second1="au=>"+arrName+" == "+arrName;
                       propositionsMap.put(arrName,Pair.of(first1, second1));
                       CPAchecker.nameToLen.put(arrName, arrLenStr);
                       CPAchecker.pureNameLen.put(arrName, arrLenStr);
                       }else{//========================================二维数组碰到结构体指针外部声明
                         arrName=function+"::"+structArrName;
                         String first1="al=>"+arrName+" < length";
                         String second1="au=>"+arrName+" == "+arrName;
                         propositionsMap.put(arrName,Pair.of(first1, second1));
                         CPAchecker.nameToLen.put(arrName, "two_array");
                         CPAchecker.twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                         CPAchecker.pureNameLen.put(arrName, "two_array");

                         arrName=function+"::"+structArrName1;
                         first1="al=>"+arrName+" < length";
                        second1="au=>"+arrName+" == "+arrName;
                        propositionsMap.put(arrName,Pair.of(first1, second1));
                        CPAchecker.nameToLen.put(arrName, "two_array");
                        CPAchecker.twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                        CPAchecker.pureNameLen.put(arrName, "two_array");
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

       //提取结束=========================================================================================================龙结束
      // long_extractPropositions(cfa,propositionsMap);
       for(CFAEdge edge:funcalledges){
         CFunctionCallEdge functionCallEdge=(CFunctionCallEdge)edge;
         //=======================================================只是方法调用，此方法无返回值，如fun(a)
         if(functionCallEdge.getFunctionCall() instanceof CFunctionCallStatement){
           Map<String,Pair<String,String>> long_propositionsMap=new HashMap<String,Pair<String,String>>();
           CFunctionCallStatement funSta=(CFunctionCallStatement)functionCallEdge.getFunctionCall();

           CFunctionCallExpression funExp=funSta.getFunctionCallExpression();
          String funname= funExp.getFunctionNameExpression().toASTString();//得到方法名字
           //System.out.println(funExp.getFunctionNameExpression().toASTString());
           List<CExpression> paras=funExp.getParameterExpressions();

           for(int i=0;i<paras.size();i++){
            CExpression para=paras.get(i);
             String parastr=para.toASTString().trim();

             Set<String> arrNames=CPAchecker.nameToLen.keySet();
             for(String arrName:arrNames){
               int a=arrName.indexOf("::");
               String changeArrName=arrName.substring(a+2).trim();
               if(parastr.contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入

                   CFunctionDeclaration fundec= (CFunctionDeclaration) funExp.getDeclaration();
                   CFunctionType funType=fundec.getType();
                  CParameterDeclaration cparadec= funType.getParameters().get(i);
                 String xingName= cparadec.getName();
                    String exArrName= xingName;
                    String function="";
                    /*if(funDec.isGlobal()){
                      function="Global";
                    }else{
                      function=node.getFunctionName();
                    }*/
                    function=funname;
                    exArrName=function+"::"+exArrName;
                    String first="al=>"+exArrName+" < length";
                    String second="au=>"+exArrName+" == "+exArrName;
                    long_propositionsMap.put(exArrName,Pair.of(first, second));
                    temp_nameToLen.put(exArrName, "function_parameter_array");



               }
             }



           }
           propositionsMap.putAll(long_propositionsMap);
           CPAchecker.nameToLen.putAll(temp_nameToLen);
         }//整个if结束，没有赋值的if
      //======================================================================有返回值的方法调用，赋值，如c=fun(a);
         if(functionCallEdge.getFunctionCall() instanceof CFunctionCallAssignmentStatement){
           Map<String,Pair<String,String>> long_propositionsMap=new HashMap<String,Pair<String,String>>();
           CFunctionCallAssignmentStatement funSta=(CFunctionCallAssignmentStatement)functionCallEdge.getFunctionCall();
            CFunctionCallExpression funRight= funSta.getRightHandSide();


            List<CExpression> paras=funRight.getParameterExpressions();
            for(int i=0;i<paras.size();i++){
              CExpression para=paras.get(i);
              String parastr=para.toASTString().trim();

              Set<String> arrNames=CPAchecker.nameToLen.keySet();
              for(String arrName:arrNames){
                int a=arrName.indexOf("::");
                String changeArrName=arrName.substring(a+2).trim();
                if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入

                  CFunctionDeclaration fundec= (CFunctionDeclaration) funRight.getDeclaration();
                  CFunctionType funType=fundec.getType();
                 CParameterDeclaration cparadec= funType.getParameters().get(i);
                String xingName= cparadec.getName();
                   String exArrName= xingName;

                     String function="";
                     /*if(funDec.isGlobal()){
                       function="Global";
                     }else{
                       function=node.getFunctionName();
                     }*/
                     CIdExpression funRightExp=(CIdExpression)funRight.getFunctionNameExpression();
                     String funName=funRightExp.getName();//得到方法名字===fun
                     function=funName;
                     exArrName=function+"::"+exArrName;
                     String first="al=>"+exArrName+" < length";
                     String second="au=>"+exArrName+" == "+exArrName;
                     long_propositionsMap.put(exArrName,Pair.of(first, second));
                     temp_nameToLen.put(exArrName, "function_parameter_array");



                }
              }

            }
            propositionsMap.putAll(long_propositionsMap);
            CPAchecker.nameToLen.putAll(temp_nameToLen);
         }

       }
  }


}
