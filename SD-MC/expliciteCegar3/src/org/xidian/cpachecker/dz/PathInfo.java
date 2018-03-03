/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.xidian.cpachecker.dz;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CLabelNode;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.CFAUtils.Loop;

import com.google.common.collect.ImmutableCollection;


public class PathInfo {
  private Map<String,Set<Integer>> uselessBranches;
  private Map<String,Integer> equalToFinal;
  private static Set<String> noUseVar=new HashSet<String>();
  private static String tmpLevel="";
  private static boolean hasUsed=false;
  private static CFANode loopHead=null;
  //private Stack<Integer> main;
  //private Stack<CFANode> secondary;
  public PathInfo(){
    uselessBranches=new HashMap<String,Set<Integer>>() ;
    equalToFinal=new HashMap<String,Integer>();
  //  main=new Stack<Integer>();
  //  secondary=new Stack<CFANode>();
  }
  public boolean analysisCFA(CFA cfa,CFANode exitNode,String function,String var,
                   String level,Map<String,Set<Integer>> uselessBranches,Map<String,Integer> equalToFinal){
    //Stack<Integer> main=new Stack<Integer>();
    Stack<CFANode> secondary=new Stack<CFANode>();
    Stack<CFANode> traverse=new Stack<CFANode>();
    traverse.add(exitNode);
    int i=0;
    String currentFunction=exitNode.getFunctionName();
    if(currentFunction.equals("max2165_get_bandwidth"))
     i=i+1-1;
    int nodeId=cfa.getFunctionHead(currentFunction).getNodeNumber();
    level=level+"&"+ nodeId;
    tmpLevel=tmpLevel+"&"+nodeId;
    while(!traverse.empty()||!secondary.empty()){
      CFANode node=null;
      if(!traverse.empty())
         node=traverse.pop();
      else{
         node=secondary.pop();
         Iterator<CFAEdge> it=node.getLeavingEdge().iterator();
         int sum=0;
         while(it.hasNext()){
           if(uselessBranches.get(level).contains(it.next().getSuccessor().getNodeNumber()))
             sum++;
         }
         if(sum==1){
           //traverse.add(node);
           if(traverse.isEmpty()){
             loopHead=null;
             boolean b=analysisLoop(node,cfa,currentFunction,function,var);
             if(!b&&loopHead!=null){
             traverse.add(loopHead);
             }
             else{
               hasUsed=true;
             }
           }
           continue;
         }
      }
      if(node.getNodeNumber()==1549)
        i=i+1;
      System.out.println(node.getNodeNumber());
      if(node instanceof CFunctionEntryNode)
        continue;
        List<CFAEdge> enteringEdges=node.getEnteringEdges();
        for(CFAEdge edge:enteringEdges){
          if(node.isLoopStart()&&((edge instanceof BlankEdge&&edge.getDescription().equals(""))||edge.getDescription().contains("Goto:")))
            continue;
          if(edge.getPredecessor() instanceof FunctionExitNode ){
            CFANode exit=edge.getPredecessor();
            String nextFunc=exit.getFunctionName();
            String nodeId1=""+cfa.getFunctionHead(nextFunc).getNodeNumber();
            if(!noUseVar.contains(nextFunc)&&!tmpLevel.contains(nodeId1)){
            boolean bool=analysisCFA(cfa,exit,function,var,level,uselessBranches,equalToFinal);
            if(!bool){
              noUseVar.add(nextFunc);
              traverse.add(node.getEnteringSummaryEdge().getPredecessor());
             // level=level.substring(0,level.lastIndexOf(nodeId));
            }
            }
            else{
              traverse.add(node.getEnteringSummaryEdge().getPredecessor());
            }
          }
          else if(edge.getPredecessor().getFunctionName().equals(function)&&
              CFAUtils.judge(edge, var)){
            equalToFinal.put(level,node.getNodeNumber());
            hasUsed=true;
          }
          else{
             if(edge.getPredecessor() instanceof CLabelNode
                 &&edge.getPredecessor().isLoopStart()){
               hasUsed=true;
               return true;
//                 boolean result= analysisLoop(edge.getPredecessor(),cfa,currentFunction,function,var);
//                 if(!result){
//                   traverse.add(edge.getPredecessor());
//                 }
//                 else{
//                   equalToFinal.put(level,node.getNodeNumber());
//                }
             }
             else if(edge instanceof CAssumeEdge){
               if(edge.getPredecessor().isLoopStart()){
                boolean result= analysisLoop(edge.getPredecessor(),cfa,currentFunction,function,var);
                if(!result){
                  traverse.add(edge.getPredecessor());
                }
                else{
                  equalToFinal.put(level,node.getNodeNumber());
                }
               }
               else if(!secondary.contains(edge.getPredecessor())){
                secondary.add(edge.getPredecessor());
                if(uselessBranches.containsKey(level)){
                  uselessBranches.get(level).add(node.getNodeNumber());
                }
                else{
                  Set<Integer> set=new HashSet<Integer>();
                  set.add(node.getNodeNumber());
                  uselessBranches.put(level,set);
                }
               }
               else{
                  Iterator<CFAEdge> it=edge.getPredecessor().getLeavingEdge().iterator();
                  while(it.hasNext()){
                    uselessBranches.get(level).remove(it.next().getSuccessor().getNodeNumber());
                  }
                  if(uselessBranches.get(level).size()==0)
                    uselessBranches.remove(level);
                  traverse.add(edge.getPredecessor());
                  secondary.remove(edge.getPredecessor());
               }
             }
             else {
               traverse.add(edge.getPredecessor());
             }
          }
        }

    }
    if(hasUsed)
    return true;
    else{
      uselessBranches.remove(level);
      return false;
    }
  }


  private boolean analysisLoop(CFANode pPredecessor,CFA pCfa, String pCurrentFunction, String pFunction, String pVar) {
    // TODO Auto-generated method stub
    ImmutableCollection<Loop> allLoops=pCfa.getLoopStructure().get().get(pCurrentFunction);
    Collection<CFANode> curLoop=null;
    Iterator<Loop> iterator=allLoops.iterator();
    while(iterator.hasNext()){
      Loop loop=iterator.next();
      if(loop.getLoopNodes().contains(pPredecessor)){
        curLoop=loop.getLoopNodes();
        loopHead=loop.getLoopHeads().iterator().next();
        break;
      }
    }
    if(curLoop==null)
      return false;
    Iterator<CFANode> it=curLoop.iterator();
    while(it.hasNext()){
      CFANode next=it.next();
      List<CFAEdge> leavings=next.getLeavingEdge();
      for(CFAEdge leave:leavings){
        CFANode suc=leave.getSuccessor() ;
       if( suc instanceof CFunctionEntryNode) {
        Set<String> functions=new HashSet<String>();
        if(noUseVar.contains(suc.getFunctionName()))
          continue;
        boolean bool=analysisFunctionForLoop((FunctionEntryNode) suc,pCfa,pFunction,pVar,functions);
        if(bool){
          return true;
        }
        else{
          noUseVar.contains(suc.getFunctionName());
        }
       }
       else if(pCurrentFunction.equals(pFunction)){
         if(CFAUtils.judge(leave, pVar)){
           return true;
         }
       }
      }
    }

   return false;
  }
  private boolean analysisFunctionForLoop(FunctionEntryNode functionEntry,CFA cfa,String function, String var,Set<String> functions){
       String curFunction=functionEntry.getFunctionName();
       Stack<CFANode> stack=new Stack<CFANode>();
       Set<Integer> hasTraverse=new HashSet<Integer>();
       if(functions.contains(curFunction)){

       }
       else{
         functions.add(curFunction);
         FunctionExitNode funcExit=functionEntry.getExitNode();
         stack.push(functionEntry);
         hasTraverse.add(functionEntry.getNodeNumber());
         while(!stack.isEmpty()){
           CFANode top=stack.pop();
           List<CFAEdge> leavings=top.getLeavingEdge();
           if(leavings!=null){
             for(CFAEdge edge:leavings){
               if(edge instanceof CFunctionCallEdge){
                 CFANode suc=edge.getSuccessor();
                 if(!functions.contains(suc.getFunctionName())){
                   functions.add(suc.getFunctionName());
                   boolean bool=analysisFunctionForLoop(cfa.getFunctionHead(suc.getFunctionName()),cfa,function,var,functions);
                   if(bool)
                     return true;
                   else{
                     stack.push(top.getLeavingSummaryEdge().getSuccessor());
                   }
                 }
               }else if(curFunction.equals(function)&&CFAUtils.judge(edge, var)){
                 return true;
               }
               else{
                 CFANode suc=edge.getSuccessor();
                 if(suc!=null&&!hasTraverse.contains(suc.getNodeNumber())){
                  stack.push(suc);
                  hasTraverse.add(suc.getNodeNumber());
                 }
               }
             }
           }

         }
       }

    return false;
  }
}
