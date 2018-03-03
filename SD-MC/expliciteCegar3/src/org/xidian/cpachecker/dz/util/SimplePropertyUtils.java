package org.xidian.cpachecker.dz.util;
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


import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.util.CFAUtils.Loop;

import com.google.common.base.Optional;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableMultimap;


public class SimplePropertyUtils {
   public static Set<CFANode> findInfiniteLoopHeadNode(CFA cfa){
     Set<CFANode> loopHeadNode=new HashSet<CFANode>();
     Optional<ImmutableMultimap<String, Loop>> loopStructure=cfa.getLoopStructure();
     Iterator<ImmutableMultimap<String, Loop>> iterator=loopStructure.asSet().iterator();
     while(iterator.hasNext()){
       ImmutableMultimap<String, Loop> next=iterator.next();
       ImmutableCollection<Loop> setLoop=next.values();
       Iterator<Loop> it=setLoop.iterator();
       while(it.hasNext()){
         Loop lp=it.next();
         CFANode headNode;
         Set<CFANode> heads=lp.getLoopHeads();
         if(heads.size()==1){
           headNode=heads.iterator().next();
           if(headNode.getNumLeavingEdges()==1){
             CFAEdge justOne=headNode.getLeavingEdge().get(0);
             if(justOne instanceof BlankEdge)
              loopHeadNode.add(headNode);
           }
         }
       }
     }
     return loopHeadNode;
  }
   public static String readProsition() throws IOException{
     FileReader fr=new FileReader("D:\\property\\propositions.txt");
     assert fr!=null;
     BufferedReader br=new BufferedReader(fr);
     String ps="";
     String s;
     while((s=br.readLine())!=null){
         ps=ps+s;
     }
     br.close();
     return ps;
   }
}
