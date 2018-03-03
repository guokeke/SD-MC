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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;


public class TxtToXml {


  private String strTxtFileName;
  private String strXmlFileName;
  public TxtToXml() {
    strTxtFileName = new String();
    strXmlFileName = new String();
   }

   public void createXml() {
    strTxtFileName = "D:\\camc\\XML\\array\\result.txt";
    strXmlFileName = "D:\\camc\\XML\\array\\resultxml.xml";
    String strTmp;
    try {
     BufferedReader inTxt = new BufferedReader(new FileReader(
       strTxtFileName));
     BufferedWriter outXml = new BufferedWriter(new FileWriter(
       strXmlFileName));
     outXml.write("<?xml version= \"1.0\" encoding=\"gb2312\"?>");
     outXml.newLine();
     outXml.write("<nullpointer>");
     int i=0;
     while ((strTmp = inTxt.readLine()) != null) {
      String arrTmp[]=strTmp.split("<->");
      outXml.newLine();
      outXml.write("    <results>");
      outXml.newLine();
      outXml.write("        <linenumber>" +i+ "</linenumber>");
      outXml.newLine();
      outXml.write("        <file>" + arrTmp[0] + "</file>");
      outXml.newLine();
      outXml.write("        <var>" + arrTmp[1] + "</var>");
      outXml.newLine();
      outXml.write("        <result>" + arrTmp[2] + "</result>");
      outXml.newLine();
      outXml.write("        <location>" + arrTmp[3] + "</location>");
      outXml.newLine();
      outXml.write("    </results>");

     }
     outXml.newLine();
     outXml.write("</nullpointer>");
     outXml.flush();
    } catch (Exception e) {
     e.printStackTrace();
    }
   }
  /*public static void main(String[] args) {
    // TODO Auto-generated method stub
    String txtName = "D:\\myeclipse1\\expliciteCegar3-1-pointer\\result.txt";
    String xmlName = "D:\\myeclipse1\\expliciteCegar3-1-pointer\\resultxml.xml";
    TxtToXml thisClass = new TxtToXml();
    //thisClass.createXml(txtName, xmlName);
  }*/

}
