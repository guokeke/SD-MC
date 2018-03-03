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
package org.xidian.cpachecker.dz;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.xidian.cpachecker.dz.proposition.PropositionInfo;


public class Proposition {
      private Map<Pair<String,String>,String> propositions;
      private Map<Pair<String,String>,CFAEdge> propEdges;
      private Map<String,String> vars=new HashMap<String,String>();
      private final static Set<String> globalVars=new HashSet<String>();
      private Pair<String,String> dAndr=Pair.of("!d","!r");
      private String funcname="";
      public Proposition(String s){
        propositions=new HashMap<Pair<String,String>,String>();
        propEdges=new HashMap<Pair<String,String>,CFAEdge>();
        setPropositions(s);
      }
      public Proposition(){
        propositions=new HashMap<Pair<String,String>,String>();
        propEdges=null;
      }
      public Proposition(Map<Pair<String,String>,String> p){
        propositions=p;
        propEdges=null;
      }
      public Set<String> getGlobalVar(){
        return globalVars;
      }
      public Map<Pair<String,String>,String> getPropositions(){
        return propositions;
      }
      public void setPropositions(String p){
         Map<String,Pair<String,String>> proLeftSide=new HashMap<String,Pair<String,String>>();
         String[] split=p.split("&&");
         assert split.length!=0;
         for(int i=0;i<split.length;i++){
              String s=split[i];
              String first=s.substring(0,s.indexOf("=>")).trim();
              String second=s.substring(s.indexOf("=>")+2).trim();
              String[] vars = second.split(" ");
              String expression="";
              String function="Global";
              String leftFunc=vars[0].substring(0,vars[0].indexOf("::")).trim();
              String leftSide=vars[0].substring(vars[0].indexOf("::")+2).trim();
              proLeftSide.put(leftSide,Pair.of(leftFunc,first));
              for(int j=0;j<vars.length;j++){
                 String var=vars[j];
                 if(var.contains("::")){
                   String func=second.substring(0,var.indexOf("::")).trim();
                   var=var.substring(var.indexOf("::")+2).trim();
                   if(func.equals("Global")){
                     globalVars.add(var);
                   }
                   else if(function.equals("Global")){
                     function=func;
                   }
                   expression=expression+var;
                 }
                 else{
                   expression=expression+var;
                 }
              }
              Pair<String,String> pair=Pair.of(first,expression);
                propositions.put(pair,function);
                Pair<String,String> pair1=Pair.of("!"+first, "!("+expression+")");
                propositions.put(pair1,function);
                funcname=function;
              /*String funcToVar=second.substring(0,second.indexOf("::")).trim();
              second=second.substring(second.indexOf("::")+2).trim();
              Pair<String,String> pair=Pair.of(first, second);
              if(funcToVar.toString().equals("")){
                propositions.put(pair,"GLOBAL");
                Pair<String,String> pair1=Pair.of("!"+first, "!("+second+")");
                propositions.put(pair1,"GLOBAL");
              }
              else{
              propositions.put(pair,funcToVar);
              Pair<String,String> pair1=Pair.of("!"+first, "!("+second+")");
              propositions.put(pair1,funcToVar);
              }*/
         }
         PropositionInfo.getInstance().setProLeftSide(proLeftSide);
      }
      public void setPropositions(Map<Pair<String,String>,String> p){
         propositions=p;
      }
      public Map<Pair<String, String>, CFAEdge> getPropEdges() {
        return propEdges;
      }

      public void setPropEdges(Map<Pair<String, String>, CFAEdge> pPropEdges) {
        propEdges= pPropEdges;
      }
      public void setPropEdges() {
        propEdges=null;
      }
      public Proposition negative(){
        Proposition non=new Proposition();
        Map<Pair<String,String>,String> nons=new HashMap<Pair<String,String>,String>();
        Map<Pair<String,String>,CFAEdge> nonsEdge=new HashMap<Pair<String,String>,CFAEdge>();
        Iterator<Pair<String,String>> it=propositions.keySet().iterator();
        while(it.hasNext()){
          Pair<String,String> pair=it.next();
          String f=pair.getFirst();
          if(f.startsWith("!")){
           nons.put(Pair.of(f,pair.getSecond()),propositions.get(pair));
           nonsEdge.put(Pair.of(f,pair.getSecond()),propEdges.get(pair));
          }
        }
        non.setPropositions(nons);
        non.setPropEdges(nonsEdge);
        return non;
      }
      public Proposition positive(){
        Proposition non=new Proposition();
        Map<Pair<String,String>,String> nons=new HashMap<Pair<String,String>,String>();
        Map<Pair<String,String>,CFAEdge> nonsEdge=new HashMap<Pair<String,String>,CFAEdge>();
        Iterator<Pair<String,String>> it=propositions.keySet().iterator();
        while(it.hasNext()){
          Pair<String,String> pair=it.next();
          String f=pair.getFirst();
          if(!f.startsWith("!")){
           nons.put(Pair.of(f,pair.getSecond()),propositions.get(pair));
           nonsEdge.put(Pair.of(f,pair.getSecond()),propEdges.get(pair));
          }
        }
        non.setPropositions(nons);
        non.setPropEdges(nonsEdge);
        return non;
      }
     /* public static void main(String[] args){
         Proposition p=new Proposition("p=>main::i==5&&Q=>alt::i==j");
         Map<Pair<String,String>,String> map=p.getPropositions();
         Set<Pair<String,String>> set=map.keySet();
         Iterator<Pair<String,String>> it=set.iterator();
         while(it.hasNext()){
           Pair<String,String> next=it.next();
           System.out.println(next+""+map.get(next));
         }
      }*/
      @Override
      public String toString(){
        StringBuilder sb=new StringBuilder();
        sb.append("propositions {");
        Iterator<Pair<String,String>> it=propositions.keySet().iterator();
        while(it.hasNext()){
          Pair<String,String> pair=it.next();
          if(sb.toString().equals("propositions {"))
           sb.append(pair.getFirst());
          else
           sb.append(","+pair.getFirst());
        }
        sb.append("}\n");
        return sb.toString();

      }

      public Pair<String, String> getdAndr() {
        return dAndr;
      }

      public void setdAndr(Pair<String, String> pDAndr) {
        dAndr = pDAndr;
      }

      public String getFuncname() {
        return funcname;
      }

      public void setFuncname(String pFuncname) {
        funcname = pFuncname;
      }

}

