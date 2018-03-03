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
package org.sosy_lab.cpachecker.util.globalinfo;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;


public class SSAMapInfo {
  private static SSAMapInfo instance;
  private Multiset<String> vars=HashMultiset.create();
  private Map<String,Map<String,Integer>> myvars=new HashMap<String,Map<String,Integer>>();
  public  static String predicates ="";
  private SSAMapInfo() {

  }
  public static SSAMapInfo getInstance() {
    if (instance == null) {
      instance = new SSAMapInfo();
    }
    return instance;
  }
  public Multiset<String> getVars(){
    return vars;
  }
  public void setVars(Multiset<String> newMap){
           Iterator<String> iterator=newMap.elementSet().iterator();
           while(iterator.hasNext()){
             String next=iterator.next();
             int count1=newMap.count(next);
             if(vars.elementSet().contains(next)){
               int count2=vars.count(next);
               vars.setCount(next,count1>count2?count1:count2);
             }
             else{
               vars.add(next);
               vars.setCount(next,count1);
             }
           }
  }
}
