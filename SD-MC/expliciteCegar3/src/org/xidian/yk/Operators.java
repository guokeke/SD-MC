/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2017  Dirk Beyer
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
package org.xidian.yk;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.predicates.Model;
import org.sosy_lab.cpachecker.util.predicates.Model.AssignableTerm;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.base.Function;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class Operators {

 // private static final ArrayList NULL = null;
  public static String valuesOfkeyVars;
  public static ArrayList<String> valuesOfAllInputVars=new ArrayList<String>();//保存输入变量的值
  public static List<Formula> tempKeyFormulas=new ArrayList<Formula>();
  public static CFAEdge tempEdge=null;
  public static CFA cfa = null;
  public static boolean isUnSat=false;
  public static Model model;
  public static boolean isLeft=false;
  public static String curKeyVar;
  public static Map<String, Term> lastTerms=new HashMap<String, Term>();
  public static Map<String, String> lastValues=new HashMap<String, String>();
  public static Map<Term, AssignableTerm> modelTermToAssign=new HashMap<Term, AssignableTerm>();
  public static Set<String> inputOrRandVar=new HashSet<String>();//保存输入变量和随机变量
  public static long time_solve=0;
  public static long time_solve1=0;
  public static long time_solve2=0;
  public static long time_solve3=0;
  public static long time_solve4=0;
  public static Stack<AbstractState> myWaitStack=new Stack<AbstractState>();
  public static boolean propertyIsTrue=false;
  public static boolean entryMain = false;
  public static final Function<PredicateAbstractState, Formula> GET_BLOCK_FORMULA
  = new Function<PredicateAbstractState, Formula>() {
      @Override
      public Formula apply(PredicateAbstractState e) {
        assert e.isAbstractionState();
        return e.getAbstractionFormula().getBlockFormula();
      }
    };
  public static void markKeyEdgesOfCFA(CFA cfa){

    Set<Integer> TranvNodeNumber=new HashSet<Integer>();

    Stack<CFANode> nodeStack=new Stack<CFANode>();
    CFANode root=cfa.getMainFunction();
    nodeStack.push(root);
    while(!nodeStack.isEmpty()){
       CFANode node=nodeStack.pop();
       //node.setTraversed(true);
       TranvNodeNumber.add(node.getNodeNumber());

       List<CFAEdge> leaving = node.getLeavingEdge();
       if(leaving!=null){
         for(CFAEdge edge:leaving){
           if(edge.getLineNumber()==807 && edge instanceof CAssumeEdge){//只遍历断言成立的分支
             if(!((CAssumeEdge) edge).getTruthAssumption()){
               edge.setNotTrans(true);//为true时不用遍历
             }
           }

           if(!edge.isKeyEdge()){
             if(isKeyEdge(edge)){//<yangkai> 分析关键变量
              edge.setKeyEdge(true);
              //System.out.println(edge);
            }
           }


           if(isInputEdge(edge)){//标记为输入边
             //是赋值边时记录被赋值的变量名
             CStatement statement = ((CStatementEdge) edge).getStatement();
             if(statement instanceof CFunctionCallAssignmentStatement){
                String varName= ((CFunctionCallAssignmentStatement) statement).getLeftHandSide().toASTString();
                inputOrRandVar.add(varName);
             }
             edge.setInputEdge(true);
           }

           CFANode sucNode=edge.getSuccessor();
           if(!TranvNodeNumber.contains(sucNode.getNodeNumber()))
           {
              nodeStack.push(sucNode);
           }
         }
       }
    }
  }
  public static boolean isKeyEdge(CFAEdge edge){
    if(edge instanceof CStatementEdge){//赋值语句
      CStatement statement = ((CStatementEdge) edge).getStatement();
      if(statement instanceof CExpressionAssignmentStatement){
         if(((CExpressionAssignmentStatement) statement).getLeftHandSide().hasKeyVar()){
           //把赋值号右边的变量加入到关键变量集合中
           ((CExpressionAssignmentStatement) statement).getRightHandSide().getKeyVars();
           return true;
         }
      }
      else if(statement instanceof CFunctionCallAssignmentStatement){
        CExpression left = ((CFunctionCallAssignmentStatement) statement).getLeftHandSide();
        if(left.hasKeyVar()){
           return true;
        }
      }
    }
    else if(edge instanceof CAssumeEdge){//判断语句
      if(((CAssumeEdge) edge).getExpression().hasInputVar()){
        edge.setInputEdge(true);
      }
      if(((CAssumeEdge) edge).getExpression().hasKeyVar()){
        return true;
      }
    }
    else if(edge instanceof CDeclarationEdge){//声明时赋值语句
       CDeclaration dec = ((CDeclarationEdge) edge).getDeclaration();
       if(dec instanceof CVariableDeclaration){
         if(KeyVar.keyVarSet.contains(dec.getName())){//声明的变量目前没有函数名
           return true;
         }
       }
    }
    else if(edge instanceof CFunctionReturnEdge){
      CFunctionSummaryEdge summary= ((CFunctionReturnEdge) edge).getSummaryEdge();
      CFunctionCall e = summary.getExpression();
      if(e instanceof CFunctionCallAssignmentStatement){
      CExpression left = ((CFunctionCallAssignmentStatement) e).getLeftHandSide();
      if(left.hasKeyVar()){
         CFANode preNode = edge.getPredecessor();
         List<CFAEdge> preNodeEnter = preNode.getEnteringEdges();
         for(CFAEdge enter:preNodeEnter){
           enter.setKeyEdge(true);
         }
         return true;
      }
    }
    }
//    else if(edge instanceof CFunctionCallEdge){
//      CFunctionSummaryEdge summary= ((CFunctionCallEdge) edge).getSummaryEdge();
//      CFunctionCall e = summary.getExpression();
//      if(e instanceof CFunctionCallAssignmentStatement){
//        CExpression left = ((CFunctionCallAssignmentStatement) e).getLeftHandSide();
//        if(left.hasKeyVar()){
//           return true;
//        }
//      }
//    }
    return false;
  }
  /*判断当前边是否是依赖于输入值的边（所有依赖于输入值的边都是赋值语句，并且赋值号右边都是random()*/
  public static boolean isInputEdge(CFAEdge edge){
    if(edge instanceof CStatementEdge){//赋值语句
      //CStatement statement = ((CStatementEdge) edge).getStatement();
      /*if(edge.getLineNumber()==807){
        return true;
      }*/

      if(edge.getRawStatement().contains("__VERIFIER_nondet_int()")||
          edge.getRawStatement().contains("rand()")){
           return true;
       }
    }
    return false;
  }
  public static void initKeyVarSet() throws IOException{//初始化关键变量集合
     FileReader fr=new FileReader("D:\\property\\propositions.txt");
      assert fr!=null;
      BufferedReader br=new BufferedReader(fr);
      String ps="";
      String s;
      while((s=br.readLine())!=null){
          ps=ps+s;
      }

      String s1[]=ps.split(" ");//根据空格进行分割
      for(int i=0; i<s1.length; i++){
        int index = s1[i].indexOf("::");
        if(index!=-1){
          String varName = s1[i].substring(index+2);
          KeyVar.keyVarSet.add(varName);
        }
      }
      br.close();
  }

  /*通过对比静态方法和动态方法分别给出的路径，找到关键条件边，并根据找到的
    关键条件边更新关键变量集合*/
  /*public static boolean findKeyVars(Path pPath) throws IOException{//更新关键变量集合
    int oldSize=KeyVar.keyVarSet.size();//添加关键变量之前的集合大小
    FileReader fr=new FileReader("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt");
    assert fr!=null;
    BufferedReader br=new BufferedReader(fr);
    String ps="";
    String s;
    while((s=br.readLine())!=null){
        ps=ps+s;
    }
    String s1[]=ps.split(" ");//根据空格进行分割

    CFAEdge lastEdge = null;//记录静态路径中最后一个条件边
    int lengthOfAssumeEdge = 0;//记录静态路径中条件边的长度
    int i = 0 ;
    List<CFAEdge> edgeList = pPath.asEdgesList();
    for(CFAEdge edge : edgeList)
    {
       if(edge instanceof CAssumeEdge){
         lastEdge = edge;
         lengthOfAssumeEdge=lengthOfAssumeEdge+1;
         String edgeToString = edge.getRawStatement();
         if(s1[i].equals(edgeToString)){
           i=i+1;
         }
         else{//不一样时将当前边中的变量加入到关键变量集合中
           ((CAssumeEdge) edge).getKeyVars();
           break;
         }
       }
    }

    if(lengthOfAssumeEdge!=s1.length){//静态和动态走过的路径长度不一致，即静态遇到了覆盖的情况
        ((CAssumeEdge) lastEdge).getKeyVars();
    }

    int newSize=KeyVar.keyVarSet.size();
    if(newSize!=oldSize){
      return true;//加入新的关键变量返回true
    }
    else{
      return false;//没有加入新的关键变量返回false
    }
  }*/
  /*将求解器给出的值写入到指定文件中,这里只写入程序中需要输入的变量的值（包括赋值为随机数或外部函数的变量）*/
  public static void writeValuesOfVars() throws IOException{

    String nameAndValues[]=valuesOfkeyVars.split("\\n");//根据换行符进行分割
    for(int i=0; i<nameAndValues.length; i++){
      String var[]=nameAndValues[i].split(" ");
      String varName=var[0];
      int size=var.length;
      String tempStr[]=var[size-1].split("\\.");
      String intValue=tempStr[0];

        if(valuesOfAllInputVars.contains(varName)){
           int index=valuesOfAllInputVars.indexOf(varName);
           valuesOfAllInputVars.set(index, intValue);//将变量名对应的位置替换为变量的值
        }
    }

    FileWriter fr=new FileWriter("values.txt");
    assert fr!=null;
    BufferedWriter br=new BufferedWriter(fr);
    String ps="";

    if(valuesOfAllInputVars!=null){
      for(int i=0; i<valuesOfAllInputVars.size(); i++){
          ps=ps+" " + valuesOfAllInputVars.get(i);
      }
    }
    System.out.println(ps);
    valuesOfAllInputVars.clear();
    br.write(ps);
    br.close();
 }
  public static boolean DynamicExe(Path pPath) throws IOException, InterruptedException {
    // TODO Auto-generated method stub
     Assert();
    Runtime run =Runtime.getRuntime();
    //mt.exec("D:\\Eclipse-TPChecker\\expliciteCegar3\\1.exe > out.txt");
    Process p = run.exec(new String[]{"cmd.exe","/c","1.exe > umc4msvl_result.txt"});
    p.waitFor();


    FileReader fr1 = new FileReader("umc4msvl_result.txt");
    assert fr1!=null;
    BufferedReader br1=new BufferedReader(fr1);
    String ps1="";
    String s1;

    while((s1=br1.readLine())!=null){
        ps1=ps1+s1;
    }
    br1.close();

    if(ps1.equals("")){
      System.out.println("#####动态验证没有结果#####");
    }

    int index=ps1.indexOf("Invalid");
    if(index!=-1){//真反例
       return true;
    }
    else{//假反例
      KeyVar.keyVarSet.add("a21");
      KeyVar.keyVarSet.add("a15");
      KeyVar.keyVarSet.add("a12");
      KeyVar.keyVarSet.add("a4");
      KeyVar.keyVarSet.add("a29");
      KeyVar.keyVarSet.add("a2");
      KeyVar.keyVarSet.add("a0");
      KeyVar.keyVarSet.add("a18");
      KeyVar.keyVarSet.add("a16");
      KeyVar.keyVarSet.add("a26");
      KeyVar.keyVarSet.add("a14");
      KeyVar.keyVarSet.add("a28");
      KeyVar.keyVarSet.add("a3");
      KeyVar.keyVarSet.add("a15");
      KeyVar.keyVarSet.add("a27");
      KeyVar.keyVarSet.add("a9");
      KeyVar.keyVarSet.add("a8");

      File file=new File("executionPath.txt");
      //计算判断边的长度
      int pathLength=pPath.size();//静态反例路径长度
      Scanner sc = new Scanner(file).useDelimiter("#");
      int i=0;
      String ps="";
      while(i<pathLength && sc.hasNext()){
         String s=sc.next();
         ps=ps+s+"#";
         i=i+1;
      }
      sc.close();
      String s2[]=ps.split("#");//s2记录动态执行路径

      CFAEdge lastEdge = null;//用来记录静态路径中最后一个条件边
      int lengthOfAssumeEdge = 0;//用来记录静态路径中条件边的长度
      String staticPath;
      i = 0 ;
      List<CFAEdge> edgeList = pPath.asEdgesList();//pPath为静态反例路径
      for(CFAEdge edge : edgeList)
      {
         if(edge instanceof CAssumeEdge){
           lastEdge = edge;
           lengthOfAssumeEdge=lengthOfAssumeEdge+1;
           String edgeToString = edge.getRawStatement();
           if(s2[i].equals(edgeToString)){
             i=i+1;
           }
           else{
             ((CAssumeEdge) edge).getKeyVars();//加入新的关键变量
             return false;
           }
         }
      }

      if(lengthOfAssumeEdge!=s2.length){//静态和动态走过的路径长度不一致且静态遇到了覆盖的情况
        ((CAssumeEdge) lastEdge).getKeyVars();
        return false;
      }

      return false;
    }
 }
 /*判断当前节点是否被前面的节点覆盖*/
 public static boolean IsCovered(ARGState curNode, ARGState preNode){
   Map<String, String> curNodeVars = curNode.getValuesOfKeyVariables();
   Map<String, String> preNodeVars = preNode.getValuesOfKeyVariables();

   for(Map.Entry<String, String> entry: curNodeVars.entrySet()){
      String varName=entry.getKey();
      /*前面节点中变量的值和当前节点中同一变量的值不相等时返回false，即不覆盖*/
      if(preNodeVars.containsKey(varName)){
        String preValue=preNodeVars.get(varName);//前面节点中名字为varName的变量的值
        String curValue=entry.getValue();//当前节点中名字为varName的变量的值
        if(!preValue.equals(curValue)){
          return false;
        }
      }
   }

   //输入变量的范围不同时不能覆盖
   String curStr=curNode.getRangeOfInputVars();
   String preStr=preNode.getRangeOfInputVars();

   //这里应该计算curStr是否蕴含preStr
   /*String s1[]=preStr.split("#");//根据#进行分割
   for(int i=0; i<s1.length; i++){
     if(!curStr.contains(s1[i])){
        return false;
     }
   }*/
   if(!curStr.equals(preStr)){
      return false;
   }
   return true;
 }
 private static boolean mystop(ARGState state, ARGState itNext) {
   // TODO Auto-generated method stub
   //boolean result=false;
   Proposition sucP = state.getProposition();
   String sucProperty = state.getProperties();
   Map<Pair<String, String>, String> sucPros = sucP.getPropositions();
   Set<Pair<String, String>> sucSet = sucPros.keySet();
   Set<Pair<String, String>> set = itNext.getProposition().getPropositions().keySet();
   String setProperty = itNext.getProperties();
   if (set.equals(sucSet) && state.getTransition().equals(itNext.getTransition())&&sucProperty.equals(setProperty)) {
       state.getChildren().clear();
       //covered.add(state);
       return true;
     }
     else{
      // state.uncover();
       return false;
     }
 }
public static boolean FindCoveredNode(AbstractState pSuccessor, Collection<AbstractState> pReached) {
  // TODO Auto-generated method stub
  if(Operators.tempEdge instanceof CReturnStatementEdge){
    return false;
  }
  Iterator it1 = pReached.iterator();

  Map<String, String> curNode1 = ((ARGState)pSuccessor).getValuesOfKeyVariables();
  //System.out.println("当前节点"+curNode1.toString());
  /*while(it1.hasNext())
  {
    ARGState itNext = (ARGState)it1.next();
    //System.out.println("已遍历节点"+itNext.getValuesOfKeyVariables());
  }*/

  Iterator it = pReached.iterator();
  while(it.hasNext()){
    ARGState itNext = (ARGState)it.next();
    boolean isCovered = IsCovered((ARGState)pSuccessor, itNext);
    if(isCovered && mystop((ARGState)pSuccessor,itNext)){
      ((ARGState)pSuccessor).setCovered(itNext);

      System.out.println(((ARGState)pSuccessor).getStateId()+"当前节点可达域为："+((ARGState)pSuccessor).getValuesOfKeyVariables());
      System.out.println(itNext.getStateId()+"覆盖节点可达域为："+itNext.getValuesOfKeyVariables().toString());


      String s1=((ARGState)pSuccessor).getRangeOfInputVars().toString();
      String s2=itNext.getRangeOfInputVars().toString();
      System.out.println(s1);
      System.out.println(s2);


      System.out.println("当前节点被覆盖");
      if(curNode1.size()<5){
        int k=0;
        k=k+1;
      }

      return true;
    }
  }
  return false;
}
public static boolean Assert() throws FileNotFoundException{
  for(int i=0; i<valuesOfAllInputVars.size(); i++){
    int value =Integer.parseInt(valuesOfAllInputVars.get(i));
    if(value==6){//输入值不在1到6之间时断言不成立
      int ii=i+1;
    }
  }
  return true;
}
}
