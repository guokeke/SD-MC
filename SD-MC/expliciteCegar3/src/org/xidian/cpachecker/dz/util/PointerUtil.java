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
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.Map;

import org.sosy_lab.common.Pair;


public class PointerUtil {
     public static void writeAllPointers(Map<String,Pair<String,String>> propositionsMap) throws IOException{
     FileWriter fw=new FileWriter("D:\\property\\allPointers.txt");
     assert fw!=null;
     BufferedWriter bw=new BufferedWriter(fw);
     Iterator<String> it=propositionsMap.keySet().iterator();
     while(it.hasNext()){
       String s=it.next();
       s=s+"<->{ "+propositionsMap.get(s).getFirst()+"&&"+propositionsMap.get(s).getSecond()+" }";
       bw.write(s+"\r\n");
       bw.flush();
     }
     bw.close();
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
