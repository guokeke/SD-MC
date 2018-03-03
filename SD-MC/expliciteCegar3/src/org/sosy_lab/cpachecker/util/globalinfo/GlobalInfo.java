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
package org.sosy_lab.cpachecker.util.globalinfo;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CCastExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFieldReference;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializer;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CElaboratedType;
import org.sosy_lab.cpachecker.cfa.types.c.CNamedType;
import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.automaton.Automaton;
import org.sosy_lab.cpachecker.util.predicates.ExtendedFormulaManager;

import com.google.common.base.Preconditions;


public class GlobalInfo {

  private static GlobalInfo instance;
  private CFAInfo cfaInfo;
  private AutomatonInfo automatonInfo = new AutomatonInfo();
  private ExtendedFormulaManager formulaManager;
  private ArrayList<Serializable> helperStorages = new ArrayList<Serializable>();
  private Configuration config = null;
  private Map<String, List<Pair<String, String>>> structType = new HashMap<String, List<Pair<String, String>>>();//mycode
  private Map<String, Integer> structSize = new HashMap<String, Integer>();//mycode
  private Map<String, String> varToType = new HashMap<String, String>();
  private Set<String> importantVars=new HashSet<String>();//保存重要的变量,即要分析值的变量
  //private Stack<Map<String, Map<String, List<String>>>> stack = new Stack<Map<String, Map<String, List<String>>>>();
  //private Map<String, Map<String, List<String>>> pointers = new HashMap<String, Map<String, List<String>>>();
  //private Map<String, List<String>> vars = new HashMap<String, List<String>>();
  //private Map<String, String> keyToValue = new HashMap<String, String>();
  private Map<String, List<String>> functionInfo = new HashMap<String, List<String>>();

  //
  //private Map<String, Map<String, Integer>> newMap = new HashMap<String, Map<String, Integer>>();
  //private Map<String, Integer> varsInfo = new HashMap<String, Integer>();
  private Map<String, Map<String, String>> newStructType = new HashMap<String, Map<String, String>>();

  private GlobalInfo() {
    //Map<String, Map<String, List<String>>> pointers = new HashMap<String, Map<String, List<String>>>();
   // stack.push(pointers);
  }
  public void addImportantVars(Set<String> set){
    importantVars.addAll(set);
  }
  public void addFunction(String f, List<String> paras) {
    functionInfo.put(f, paras);
  }

  public void addStructSize(String s, int size) {
    structSize.put(s, size);
  }

  public void addStructType(String type, Map<String, String> mem) {
    newStructType.put(type, mem);
  }

  public void addVarToType(String v, String type) {
    varToType.put(v, type);
  }

  public static GlobalInfo getInstance() {
    if (instance == null) {
      instance = new GlobalInfo();
    }
    return instance;
  }


  public Configuration getConfig() {
    return config;
  }


  public void setConfig(Configuration pConfig) {
    config = pConfig;
  }

  public void storeCFA(CFA cfa) {
    cfaInfo = new CFAInfo(cfa);
  }

  public CFAInfo getCFAInfo() {
    Preconditions.checkState(cfaInfo != null);
    return cfaInfo;
  }

  public void storeAutomaton(Automaton automaton) {
    automatonInfo.register(automaton);
  }

  public AutomatonInfo getAutomatonInfo() {
    Preconditions.checkState(automatonInfo != null);
    return automatonInfo;
  }

  public void storeFormulaManager(ExtendedFormulaManager formulaManager) {
    this.formulaManager = formulaManager;
  }

  public ExtendedFormulaManager getFormulaManager() {
    Preconditions.checkState(formulaManager != null);
    return formulaManager;
  }

  public int addHelperStorage(Serializable e) {
    helperStorages.add(e);
    return helperStorages.size() - 1;
  }

  public Serializable getHelperStorage(int index) {
    return helperStorages.get(index);
  }

  public int getNumberOfHelperStorages() {
    return helperStorages.size();
  }


  public Map<String,Map<String, String>> getStructType() {
    return newStructType;
  }


  public void setStructType(Map<String, List<Pair<String, String>>> pStructType) {
    structType = pStructType;
  }
  public List<String> getMyString(CFAEdge edge){
    List<String> list=new ArrayList<String>();
    if(edge instanceof CDeclarationEdge){
      String des=edge.getDescription().toString();
      CDeclaration dec=((CDeclarationEdge) edge).getDeclaration();
      if(dec instanceof CVariableDeclaration){
        CInitializer init=((CVariableDeclaration) dec).getInitializer();
        if(init instanceof CInitializerExpression){
          CExpression exp=((CInitializerExpression) init).getExpression();
          exp.setMyString(list);
        }
      }
    }
    else if(edge instanceof CStatementEdge){
      CStatement stat=((CStatementEdge) edge).getStatement();
      if(stat instanceof CExpressionAssignmentStatement){
        CExpression right=((CExpressionAssignmentStatement) stat).getRightHandSide();
        right.setMyString(list);
      }
    }
    return list;
  }
  public boolean analysis(CFAEdge edge, String func,Stack<Pair<Map<String, Map<String, Integer>>,Map<String, Integer>> > stack1) {
    Pair<Map<String, Map<String, Integer>>,Map<String, Integer>> pair=null;
    Map<String, Map<String, Integer>> newMap=null;
    Map<String, Integer> varsInfo=null;
    //System.out.println(stack1.empty());
    if (!stack1.isEmpty()){
      pair=stack1.peek();
      newMap=pair.getFirst();
      varsInfo=pair.getSecond();
    }
    else{
      newMap=new HashMap<String, Map<String, Integer>>();
      varsInfo=new HashMap<String,Integer>();
      pair=Pair.of(newMap,varsInfo);
      stack1.push(pair);
    }
    if (edge instanceof CDeclarationEdge && ((CDeclarationEdge) edge).getDeclaration() instanceof CVariableDeclaration) {
      CVariableDeclaration declaration = (CVariableDeclaration) ((CDeclarationEdge) edge).getDeclaration();
      String name = declaration.getName();
      name = func + "::" + name;
      CType type = declaration.getType();
      if (type instanceof CPointerType ) {
        String typename="";
        CNamedType type1=null;
        if(((CPointerType) type).getType() instanceof CNamedType){
        type1 = (CNamedType) ((CPointerType) type).getType();
        typename = type1.getName();
        }
        else if(((CPointerType) type).getType() instanceof CElaboratedType){
            typename=((CElaboratedType) ((CPointerType) type).getType()).getName();
        }
        if (structType.keySet().contains(typename)) {
          List<String> list = null;
          // String var = name;
          // String varTo = name;
          //Map<String, List<String>> pointToVar = new HashMap<String, List<String>>();
           CInitializer init = declaration.getInitializer();
          if (init != null && init instanceof CInitializerExpression) {
            list = new ArrayList<String>();
            CExpression expression = ((CInitializerExpression) init).getExpression();
            expression.setVarName(list);
          }
          if (list == null || list.size() == 0) {
            if(init instanceof CInitializerExpression
                &&((CInitializerExpression) init).getExpression() instanceof CCastExpression){
              CCastExpression exp=(CCastExpression) ((CInitializerExpression) init).getExpression();
              if(exp.getOperand() instanceof CIdExpression){//x=p;
                CIdExpression idExp=(CIdExpression) exp.getOperand();
                String id=idExp.getName();
                if(varsInfo.keySet().contains(id)&&varsInfo.get(id)==1){
                  Map<String, Integer> map = new HashMap<String, Integer>();
                  Map<String, String> type2 = newStructType.get(typename);
                  Iterator<String> it = type2.keySet().iterator();
                  while (it.hasNext()) {
                    map.put(it.next(), 1);
                  }
                  //varsInfo.put(var, 1);
                  newMap.put(name, map);
                  varsInfo.put(name, 1);
                  return true;
                }
              }
            }
            Map<String, Integer> map = new HashMap<String, Integer>();
            Map<String, String> type2 = newStructType.get(typename);
            Iterator<String> it = type2.keySet().iterator();
            while (it.hasNext()) {
              map.put(it.next(), 0);
            }
            //varsInfo.put(var, 1);
            newMap.put(name, map);
            varsInfo.put(name, 0);
          }
          else {
            Map<String, String> members = newStructType.get(typename);//Map<var,type>
            int size = list.size();
            String curVar = func + "::" + list.get(size - 1);
            if (size == 1 && varsInfo.containsKey(curVar)) {
              varsInfo.put(name, varsInfo.get(curVar));
              Map<String,Integer> curMap=newMap.get(curVar);
              newMap.put(name, curMap);
            }
            else if (varsInfo.containsKey(curVar) && varsInfo.get(curVar) == 1) {
              int count = 0;
              String newvar = name;
              List<String> listTypes = new ArrayList<String>();
              Set<String> norepeat = new HashSet<String>();
              for (int i = size - 2; i >= 0; i--) {
                String curMem = list.get(i);
                String memType = members.get(curMem);
                listTypes.add(memType);
                norepeat.add(curMem);
                newvar = newvar + "." + curMem;
                if (norepeat.size() == 1) {
                  count += 1;
                }
                else {
                  members = newStructType.get(memType);
                }
              }
              if (count == size - 1&&newMap.keySet().contains(curVar)&&newMap.get(curVar).size()!=0) {
                //String checkType=mytypes.get(1);
                Map<String, Integer> curMap = newMap.get(curVar);
                String mem = list.get(1);
                int sum = curMap.get(mem);
                if (sum >= count) {
                  Map<String, Integer> varMap = new HashMap<String, Integer>();
                  varMap.put(mem, sum - count);
                  newMap.put(name, varMap);
                  varsInfo.put(name, 1);
                }
              }
              else if(newMap.keySet().contains(curVar)&&newMap.get(curVar).size()!=0){
                String first = newvar.substring(0, newvar.lastIndexOf("."));
                String mem = newvar.substring(newvar.lastIndexOf(".") + 1);
                if (varsInfo.containsKey(first) && varsInfo.get(first) == 1) {
                  Map<String, Integer> memMap = newMap.get(first);
                  int sum = memMap.get(mem);
                  if (sum >= 1) {
                    varsInfo.put(name, 1);
                    if (newMap.keySet().contains(newvar)) {
                      newMap.put(name, newMap.get(newvar));
                    }
                  }
                }
              }
            }
          }
        }
        else if(importantVars.contains(name)){
          CInitializer init = declaration.getInitializer();
          if(init!=null)
            varsInfo.put(name,1);
        }
      }
      else if(type instanceof CElaboratedType||type instanceof CNamedType){
        String typename="";
        if(type instanceof CNamedType){
          typename=((CNamedType) type).getName();
          }
          else if(type instanceof CElaboratedType){
              typename=((CElaboratedType)type).getName();
          }
        if (structType.keySet().contains(typename)) {
          List<String> list = null;
          // String var = name;
          // String varTo = name;
          //Map<String, List<String>> pointToVar = new HashMap<String, List<String>>();
           CInitializer init = declaration.getInitializer();
          if (init != null && init instanceof CInitializerExpression) {
            list = new ArrayList<String>();
            CExpression expression = ((CInitializerExpression) init).getExpression();
            expression.setVarName(list);
          }
          if(list==null){
            Map<String, Integer> map = new HashMap<String, Integer>();
            //String vtype=varToType.get(var);
            if(newStructType.keySet().contains(typename)){
            Map<String, String> vtype = newStructType.get(typename);
            Iterator<String> it = vtype.keySet().iterator();
            while (it.hasNext()) {
              map.put(it.next(), 1);
            }
            varsInfo.put(name, 1);
            newMap.put(name, map);
            varToType.put(name, typename);
            }
          }
          else if(list.size()==1){
            String varR=list.get(0);
            if(newStructType.keySet().contains(typename)&&
                varsInfo.keySet().contains(varR)&&varsInfo.get(varR)==1){
              Map<String, Integer> map = new HashMap<String, Integer>();
              Map<String, String> vtype = newStructType.get(varToType.get(typename));
              Iterator<String> it = vtype.keySet().iterator();
              while (it.hasNext()) {
                map.put(it.next(), 1);
              }
              varsInfo.put(name, 1);
              newMap.put(name, map);
              varToType.put(name, typename);
            }
          }
        }

      }
      else if(importantVars.contains(name)){
        CInitializer init = declaration.getInitializer();
        if(init!=null)
          varsInfo.put(name,1);
      }

    }
    else if (edge instanceof CStatementEdge) {

      CStatement statement = ((CStatementEdge) edge).getStatement();
      if (statement instanceof CExpressionAssignmentStatement) {
        CExpression left = ((CExpressionAssignmentStatement) statement).getLeftHandSide();
        CExpression right = ((CExpressionAssignmentStatement) statement).getRightHandSide();
        //analysis left
        String lv = "";
        CType typeL = null;
        String typenameL = "";
        List<String> listL = new ArrayList<String>();//标记leftSide是否为r->next->d..这种形式

        if (left instanceof CIdExpression) {
          CSimpleDeclaration declaration = ((CIdExpression) left).getDeclaration();
          typeL = declaration.getType();
          lv = func + "::" + declaration.getName();
          if (typeL instanceof CPointerType ) {
            if(((CPointerType) typeL).getType() instanceof CNamedType){
            typenameL = ((CNamedType) ((CPointerType) typeL).getType()).getName();
            }
            else if(((CPointerType) typeL).getType() instanceof CElaboratedType){
                typenameL=((CElaboratedType) ((CPointerType) typeL).getType()).getName();
            }
          }
        }
        else if (left instanceof CFieldReference) {//现在只处理:r->next->d..这种情况
          left.setVarName(listL);
        }
        //analysis right
        String rv = "";//rightSide是一个只是变量名
        CType typeR = null;
        String typenameR = "";
        List<String> listR = new ArrayList<String>();//现在只处理:r->next->d..这种情况
        if (right instanceof CIdExpression) {
          CSimpleDeclaration declaration = ((CIdExpression) right).getDeclaration();
          if (declaration != null) {
            typeR = declaration.getType();
            rv = func + "::" + declaration.getName();
            if (typeR instanceof CPointerType ) {
              if(((CPointerType) typeR).getType() instanceof CNamedType){
              typenameR = ((CNamedType) ((CPointerType) typeR).getType()).getName();
              }
              else if(((CPointerType) typeR).getType() instanceof CElaboratedType){
                  typenameR=((CElaboratedType) ((CPointerType) typeR).getType()).getName();
              }
            }
          }
        }
        else if (right instanceof CFieldReference) {
          right.setVarName(listR);
        }
        else if(right instanceof CUnaryExpression){
          right.setVarName(listR);
        }
        else if(right instanceof CLiteralExpression){
          right.setVarName(listR);
        }
        //start compute
        if (!lv.equals("") && newMap.keySet().contains(lv)) {
          String name = lv;
          if(rv.equals("")&&listR.size() == 0 ){
            varsInfo.remove(lv);
            //newMap.get(lv).clear();
            newMap.remove(lv);
          }
          else if (!rv.equals("")) {//r=q;
            if(varsInfo.keySet().contains(rv)){
            varsInfo.put(lv, varsInfo.get(rv));
            newMap.put(lv, newMap.get(rv));
            }
            else{
              varsInfo.remove(lv);
              //newMap.get(lv).clear();
              newMap.remove(lv);
            }
          }
          else if (listR.size() != 0 && newMap.keySet().contains(func + "::" + listR.get(listR.size() - 1))) {//r=p->next
            // if (|| listR.size() == 0) {
            //newMap.put(name,list);
            //  varsInfo.put(name, 0);
            //}
            //else {
            int size = listR.size();//
            rv = func + "::" + listR.get(size - 1);//if r->next->d ,then curVar=r; listR={d,next,r}
            typenameR = varToType.get(rv);//rightSide  owner变量的类型
            Map<String, String> members = newStructType.get(typenameR);//对应的结构体成员
            boolean varContain=varsInfo.containsKey(rv);
            if (varContain&& varsInfo.get(rv) == 1) {//curVar已经被保存,有他的信息
              int count = 0;
              String newvar = rv;
              List<String> listTypes = new ArrayList<String>();
              //782-796:判断是r->next->next...还是r->a->b...
              Set<String> norepeat = new HashSet<String>();
              for (int i = size - 2; i >= 0; i--) {
                String curMem = listR.get(i);
                String memType = members.get(curMem);
                listTypes.add(memType);
                norepeat.add(curMem);
                newvar = newvar + "." + curMem;
                if (norepeat.size() == 1) {
                  count += 1;
                }
                else {
                  members = newStructType.get(memType);
                }
              }
              boolean contain=newMap.keySet().contains(rv);
              if (count == size - 1&&contain&&newMap.get(rv).size()!=0) {//是r->next->next->next..这种形式
                //String checkType=mytypes.get(1);
                Map<String, Integer> curMap = newMap.get(rv);
                String mem = listR.get(0);//得到最外面的变量
                int sum = curMap.get(mem);//得到他可以连续的次数
                Map<String, Integer> varMap = new HashMap<String, Integer>();
                if (sum >= count) {
                  varMap.put(mem, sum - count);
                  newMap.put(name, varMap);
                  if(sum - count==0)
                  varsInfo.put(name, 0);
                  else
                  varsInfo.put(name, 1);
                }
                else{
                  varMap.put(mem,0);
                  newMap.put(name, varMap);
                  varsInfo.put(name,0);

                }
              }
              else if(contain&&newMap.get(rv).size()!=0){//是r->a->b...这种形式
                String first = newvar.substring(0, newvar.lastIndexOf("."));//if r->a->b then first=r.a
                String mem = newvar.substring(newvar.lastIndexOf(".") + 1); //mem=b
                if (varsInfo.containsKey(first) && varsInfo.get(first) == 1) {//变量集合包含r.a
                  Map<String, Integer> memMap = newMap.get(first);
                  int sum = memMap.get(mem);
                  if (sum >= 1) {
                    varsInfo.put(name, 1);
                    if (newMap.keySet().contains(newvar)) {
                      newMap.put(name, newMap.get(newvar));
                    }
                  }
                }
              }
            }
            else if(varContain){
              varsInfo.put(lv, varsInfo.get(rv));
              newMap.put(lv, newMap.get(rv));
            }
            else{
              varsInfo.remove(lv);
              //newMap.get(lv).clear();
              newMap.remove(lv);
            }
            //}
          }
        }
        else if (listL.size() != 0 && newMap.keySet().contains(func + "::" + listL.get(listL.size() - 1))) {//r->a=r||r->a=p->b
          boolean ltype = false;//if leftSide=r->next->next.. then  true  else leftSide=r->a->b  then false
          int sumL = 0;
          int countL = 0;
          String nameL = "";
          Map<String, Integer> varMapL = null;
          String memberL = "";
          List<String> listTypesL = new ArrayList<String>();
          //if (listL == null || listL.size() == 0) {

          // }
          // else {
          int sizeL = listL.size();
          nameL = func + "::" + listL.get(sizeL - 1);//得到owner变量   if r->a->b  ,nameL=r
          typenameL = varToType.get(nameL);//得到owner的类型
          Map<String, String> membersL = newStructType.get(typenameL);//对应的结构体成员
          if (varsInfo.keySet().contains(nameL) && varsInfo.get(nameL) == 1) {//变量集合包含nameL
            String newvar = nameL;
            Set<String> norepeat = new HashSet<String>();
            for (int i = sizeL - 2; i >= 0; i--) {
              String curMem = listL.get(i);
              String memType = membersL.get(curMem);
              listTypesL.add(memType);
              norepeat.add(curMem);
              newvar = newvar + "." + curMem;
              if (norepeat.size() == 1) {
                countL += 1;
              }
              else {
                membersL = newStructType.get(memType);
              }
            }
            if (countL == sizeL - 1) {
              //String checkType=mytypes.get(1);
              ltype = true;
              Map<String, Integer> curMap = newMap.get(nameL);
              memberL = listL.get(0);
              sumL = curMap.get(memberL);
              if (sumL >= countL) {
                varMapL = curMap;
              }
            }
            else {
              nameL = newvar;
              varMapL=new HashMap<String,Integer>();
            }
          }
          // }
          //829-890左操作数处理完,变量提取ok,
          if (!rv.equals("") && varsInfo.keySet().contains(rv)) {//右操作数的形式:r->next=p;
            if (varMapL != null) {
              if (ltype) {//左操作数为r->next->next...
                if (varsInfo.get(rv) == 1) {
                  Map<String, Integer> rvMap = newMap.get(rv);
                  int rvMapsize=rvMap.get(memberL);
                  varMapL.put(memberL, countL);
                  varMapL.put(memberL, countL+rvMapsize);
                 /* Iterator<String> it = rvMap.keySet().iterator();
                  while (it.hasNext()) {
                    String next = it.next();
                    if (memberL.equals(next)) {
                      int varnum = varMapL.get(next);
                      varMapL.put(next, rvMap.get(next) + varnum);
                      break;
                    }
                    else {
                      varMapL.put(next, rvMap.get(next));
                    }
                  }*/
                }
                else {
                  varMapL.put(memberL, countL+1);//r->next->next=q&&没有q的信息,则 r->next->next=0
                }
              }
              else {
                if (varsInfo.get(rv) == 1) {
                  Map<String, Integer> rvMap = newMap.get(rv);
                  newMap.put(nameL, rvMap);
                }

              }
            }

          }
          else if (listR.size() != 0 && newMap.keySet().contains(func + "::" + listR.get(listR.size() - 1))) {//r->a=p->next
            //if (listR.size() == 0) {
            //newMap.put(name,list);
           // varsInfo.put(nameL, 0);
            //  }
            // else {
            typenameR = varToType.get(func + "::" + listR.get(listR.size() - 1));
            int size = listR.size();
            rv = func + "::" + listR.get(size - 1);
            Map<String, String> members = newStructType.get(typenameR);
            if (varsInfo.containsKey(rv) && varsInfo.get(rv) == 1) {
              int count1 = 0;
              String newvar = rv;
              List<String> listTypes1 = new ArrayList<String>();
              Set<String> norepeat = new HashSet<String>();
              for (int i = size - 2; i >= 0; i--) {
                String curMem = listR.get(i);
                String memType = members.get(curMem);
                listTypes1.add(memType);
                norepeat.add(curMem);
                newvar = newvar + "." + curMem;
                if (norepeat.size() == 1) {
                  count1 += 1;
                }
                else {
                  members = newStructType.get(memType);
                }
              }
              if (count1 == size - 1) {
                //String checkType=mytypes.get(1);
                Map<String, Integer> curMap = newMap.get(rv);
                String mem = listR.get(0);
                int sum1 = curMap.get(mem);
                if (varMapL != null) {
                  if (ltype) {
                    if (varsInfo.keySet().contains(rv) && varsInfo.get(rv) == 1) {
                      Map<String, Integer> rvMap = newMap.get(rv);
                      int rvMapsize=rvMap.get(mem);
                      varMapL.put(memberL, countL);
                      varMapL.put(memberL,countL+rvMapsize  - count1+1);
                    }
                    else {
                      varMapL.put(memberL, countL);
                    }
                  }
                  else {
                    if (varsInfo.get(rv) == 1) {
                      Map<String, Integer> rvMap = newMap.get(rv);
                      int rvMapsize=rvMap.get(mem);
                      varMapL.put(memberL, countL);
                      varMapL.put(memberL,countL+rvMapsize  - count1);
                      //Map<String, Integer> rvMap = newMap.get(rv);
                      newMap.put(nameL, varMapL);
                    }
                  }
                }
              }
              else {
                rv=newvar;
                if (varsInfo.containsKey(rv) && varsInfo.get(rv) == 1) {
                  //Map<String, Integer> memMap = newMap.get(rv);
                  if (varMapL != null) {
                    if (ltype) {//左操作数为r->next->next...
                      if (varsInfo.get(rv) == 1) {
                        Map<String, Integer> rvMap = newMap.get(rv);
                        int rvMapsize=rvMap.get(memberL);
                        varMapL.put(memberL, countL+1);
                        varMapL.put(memberL,countL+1+rvMapsize);
                       //varMapL.put(memberL, countL+1);
                        //Map<String, Integer> rvMap = newMap.get(rv);
                        //Iterator<String> it = rvMap.keySet().iterator();
                        /*while (it.hasNext()) {
                          String next = it.next();
                          if (varMapL.keySet().contains(next)) {
                            int varnum = varMapL.get(next);
                            varMapL.put(next, rvMap.get(next) + varnum);
                          }
                          else {
                            varMapL.put(next, rvMap.get(next));
                          }
                        }*/
                      }
                      else {
                        varMapL.put(memberL, countL+1);//r->next->next=q&&没有q的信息,则 r->next->next=0
                      }
                    }
                    else {
                      if (varsInfo.get(rv) == 1) {
                        Map<String, Integer> rvMap = newMap.get(rv);
                        newMap.put(nameL, rvMap);
                      }

                    }
                  }

                }
              }
            }
          }
        }
        return true;
      }
      else if(statement instanceof CFunctionCallAssignmentStatement){
        CExpression left = ((CFunctionCallAssignmentStatement) statement).getLeftHandSide();
        CFunctionCallExpression right = ((CFunctionCallAssignmentStatement) statement).getRightHandSide();
        if(left instanceof CIdExpression &&((CIdExpression) left).getName().contains("__CPAchecker_TMP_0")){
          String name=((CIdExpression) left).getName();
          if(right.getFunctionNameExpression() instanceof CIdExpression){
            CIdExpression funId=(CIdExpression) right.getFunctionNameExpression();
            String functionname=funId.getName();
            if(functionname.matches("[rk]*malloc")){
              varsInfo.put(name, 1);
            }
          }
        }
      }
      else if(statement instanceof CFunctionCallStatement){
        CFunctionCallExpression exp=((CFunctionCallStatement) statement).getFunctionCallExpression();
        if(exp.getFunctionNameExpression() instanceof CIdExpression){
          CIdExpression idExp=(CIdExpression) exp.getFunctionNameExpression();
          String functionname=idExp.getName();
          if(functionname.equals("free")){
            CExpression pe=exp.getParameterExpressions().get(0);
            List<String> l = new ArrayList<String>();
            if (pe instanceof CIdExpression) {
              CSimpleDeclaration declaration = ((CIdExpression) pe).getDeclaration();
              CType type = declaration.getType();
              String v = declaration.getName();
              if (type instanceof CPointerType) {
                l.add(v);
              }
            }
            else if (pe instanceof CFieldReference) {
              pe.setVarName(l);
            }
            if(l.size()==1){
              String curVar = edge.getPredecessor().getFunctionName() + "::" + l.get(0);
              varsInfo.put(curVar ,0);
              Map<String,Integer> curMap=newMap.get(curVar);
              if(curMap!=null&&curMap.size()!=0){
                curMap.clear();
              }

            }
            else if(l.size()==2){
              String curVar = edge.getPredecessor().getFunctionName() + "::" + l.get(1);
              String mem=l.get(0);
              if(newMap.keySet().contains(curVar)){
                Map<String,Integer> curMap=newMap.get(curVar);
                if(curMap.get(mem)>=1)
                 curMap.put(mem,1);
              }
            }
            else if(l.size()>2){
              int size=l.size();
              String curVar = edge.getPredecessor().getFunctionName() + "::" + l.get(size - 1);
              if(newMap.keySet().contains(curVar)){
                Map<String, Integer> curMap = newMap.get(curVar);
                int curList =0;// curMap.get(varsInfo.get(curVar));
                //String typename = varToType.get(curVar);
               // List<Pair<String, String>> members = structType.get(typename);
                Set<String> setList=new HashSet<String>();
                String mem="";
                l.remove(size-1);
                //l.remove(size);
                setList.addAll(l);
                if(setList.size()==1){
                    mem=l.get(0);
                }
                if(mem.equals("")){
                  for (int j =l.size()-1; j >= 0; j--){
                    curVar=curVar+"."+l.get(j);
                  }
                  if (newMap.keySet().contains(curVar)) {
                    newMap.remove(curVar);
                    if (varsInfo.keySet().contains(curVar)) {
                      varsInfo.remove(curVar);
                    }
                  }
                }
                else{
                  size=l.size();
                  curList = curMap.get(mem);
                  Map<String, Integer> fpMap=new HashMap<String,Integer>();
                  if(curList>size){
                    curMap.put(mem,size);
                  }
                  else{
                  //  fpMap.put(mem,0);
                  //  newMap.put(fp,fpMap);
                  //  varsInfo.put(fp,0);
                  }
                }
              }

            }

          }
        }
      }
    }
    else if (edge instanceof CFunctionCallEdge) {
      CFunctionCall exp = ((CFunctionCallEdge) edge).getFunctionCall();
      List<CExpression> paras = exp.getFunctionCallExpression().getParameterExpressions();//形参
      List<List<String>> ptmps = new ArrayList<List<String>>();
      String fun=edge.getSuccessor().getFunctionName();
      int i = -1;
      for (CExpression pe : paras) {
        i++;
        if (pe instanceof CIdExpression) {
          CSimpleDeclaration declaration = ((CIdExpression) pe).getDeclaration();
          CType type = declaration.getType();
          String v = declaration.getName();
          List<String> list = new ArrayList<String>();
          list.add(String.valueOf(i));
          if (type instanceof CPointerType) {
            list.add(v);
            ptmps.add(list);
          }
        }
        else if (pe instanceof CFieldReference) {
          List<String> list = new ArrayList<String>();
          list.add(String.valueOf(i));
          pe.setVarName(list);
          if (list.size() != 0) {
            ptmps.add(list);
          }
        }
      }
      newMap=new HashMap<String, Map<String, Integer>>();
      varsInfo=new HashMap<String,Integer>();
      pair=Pair.of(newMap,varsInfo);
      stack1.push(pair);
      //pointers = stack.peek();
      List<String> para = functionInfo.get(func);
      for (List<String> l : ptmps) {
        if (l.size() == 2) {//参数都是一个变量r
          int index = Integer.valueOf(l.get(0));
          String fp = fun + "::" + para.get(index);//形参
          String ap = edge.getPredecessor().getFunctionName() + "::" + l.get(1);//实参
          if (newMap.keySet().contains(ap)) {
            newMap.put(fp, newMap.get(ap));
            if (varsInfo.keySet().contains(ap)) {
              varsInfo.put(fp, varsInfo.get(ap));
            }
          }
        }
        else {
          int index = Integer.valueOf(l.get(0));//形参的位置
          String fp = func + "::" + para.get(index);//第index个形参
          int size = l.size();
          String curVar = edge.getPredecessor().getFunctionName() + "::" + l.get(size - 1);
          if(newMap.keySet().contains(curVar)){
            Map<String, Integer> curMap = newMap.get(curVar);
            int curList =0;// curMap.get(varsInfo.get(curVar));
            String typename = varToType.get(curVar);
            List<Pair<String, String>> members = structType.get(typename);
            Set<String> setList=new HashSet<String>();
            String mem="";
            l.remove(size-1);
            //l.remove(size);
            setList.addAll(l);
            if(setList.size()==2){
                mem=l.get(1);
            }
            if(mem.equals("")){
              for (int j =l.size()-1; j >= 1; j--){
                curVar=curVar+"."+l.get(j);
              }
              if (newMap.keySet().contains(curVar)) {
                newMap.put(fp, newMap.get(curVar));
                if (varsInfo.keySet().contains(curVar)) {
                  varsInfo.put(fp, varsInfo.get(curVar));
                }
              }
            }
            else{
              size=l.size();
              curList = curMap.get(mem);
              Map<String, Integer> fpMap=new HashMap<String,Integer>();
              if(curList>size){
                fpMap.put(mem,curList-1);
                newMap.put(fp,fpMap);
                varsInfo.put(fp,1);
              }
              else{
              //  fpMap.put(mem,0);
              //  newMap.put(fp,fpMap);
              //  varsInfo.put(fp,0);
              }
            }
          }
        }
      }
     // stack.push(pointers1);

    }
    else if (edge instanceof CFunctionReturnEdge || edge instanceof CReturnStatementEdge) {
      if (edge.getSuccessor() instanceof FunctionExitNode)
        stack1.pop();
    }
    return false;
  }

  public int update(String var,Map<String, Map<String, Integer>> newMap,Map<String, Integer> varsInfo) {
    if(varsInfo.keySet().contains(var)&&varsInfo.get(var)==1)
      return 0;
    Map<String, Integer> map = new HashMap<String, Integer>();
    String vtype=varToType.get(var);
    if(newStructType.keySet().contains(vtype)){
    Map<String, String> type = newStructType.get(varToType.get(var));
    Iterator<String> it = type.keySet().iterator();
    while (it.hasNext()) {
      map.put(it.next(), 1);
    }
    varsInfo.put(var, 1);
    newMap.put(var, map);
    }
    else{
      varsInfo.put(var,1);
    }

    return 1;
  }

//  public int isNull(String var,Map<String, Map<String, Integer>> newMap,Map<String, Integer> varsInfo) {
//    if(!varsInfo.keySet().contains(var)){
//      return -1;
//    }
//    if(varsInfo.get(var)==1)
//      return 0;
//    return 1;
//  }

  public int isNull(String var, Stack<Pair<Map<String, Map<String, Integer>>, Map<String, Integer>>> stack1) {
    // TODO Auto-generated method stub
    Pair<Map<String, Map<String, Integer>>,Map<String, Integer>> pair=null;
    Map<String, Map<String, Integer>> newMap=null;
    Map<String, Integer> varsInfo=null;
   // System.out.println(stack1.empty());
    if (!stack1.isEmpty()){
      pair=stack1.peek();
      newMap=pair.getFirst();
      varsInfo=pair.getSecond();
      if(!varsInfo.keySet().contains(var)){
        return -1;
      }
      if(varsInfo.get(var)==1/*&&newMap.keySet().contains(var)&&newMap.get(var).size()!=0*/)
        return 0;
      else
        return 1;
    }
    else{
      return -1;
    }
  }

  public int update(String var, Stack<Pair<Map<String, Map<String, Integer>>, Map<String, Integer>>> stack1,int flag) {
    // TODO Auto-generated method stub
    Pair<Map<String, Map<String, Integer>>,Map<String, Integer>> pair=null;
    Map<String, Map<String, Integer>> newMap=null;
    Map<String, Integer> varsInfo=null;
    System.out.println(stack1.empty());
    if (!stack1.isEmpty()){
      pair=stack1.peek();
      newMap=pair.getFirst();
      varsInfo=pair.getSecond();
    }
    else{
     newMap=new HashMap<String,Map<String,Integer>>();
     varsInfo=new HashMap<String,Integer>();
     pair=Pair.of(newMap,varsInfo);
     stack1.push(pair);
    }
      //return 0;
//    if(varsInfo.keySet().contains(var)&&varsInfo.get(var)==1)
//      return 0;
    Map<String, Integer> map = new HashMap<String, Integer>();
    String vtype=varToType.get(var);
    if(newStructType.keySet().contains(vtype)){
    Map<String, String> type = newStructType.get(vtype);
    Iterator<String> it = type.keySet().iterator();
    if(flag==1){
      while (it.hasNext()) {
        map.put(it.next(), 1);
      }
      varsInfo.put(var, 1);
      newMap.put(var, map);
    }
    else if(flag==0){
      while (it.hasNext()) {
        map.put(it.next(), 0);
      }
      varsInfo.put(var, 0);
      newMap.put(var, map);
    }
    }
    else{
      if(flag==1)
       varsInfo.put(var,1);
      else
       varsInfo.put(var,0);
    }

    return 1;
  }
  public void printImportantVars(){
    System.out.println(importantVars);
  }
//  public void print() {
//    //System.out.println(structType);
//    // System.out.println(pointers.size());
//
//    System.out.println("newMap=" + newMap);
//    System.out.println("varsInfo= " + varsInfo);
//    //System.out.println("keyToValue= " + keyToValue);
//    //System.out.println("varToType=" + varToType);
//  }

}
