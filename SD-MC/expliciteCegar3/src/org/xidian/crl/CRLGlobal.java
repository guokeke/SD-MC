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
package org.xidian.crl;

import java.util.ArrayList;
import java.util.List;

import org.sosy_lab.common.Pair;


public class CRLGlobal {


  private static CRLGlobal instance;
  public static String nostr=null;//记录数组[]中数值


  private int funcallnub=0;//记录所有方法调用个数总和


  private int funFlgLen=0;//记录方法层数
  private String funGloLen;//记录方法里的所有形参对应的数组定义长度
 // private boolean funtwoarrflag=false;











  private String pointerGloLen="0";//记录数组下标值
  private String firstPointerGloLen="0";//记录数组第一个值
  private String secondPointerGloLen="0";//记录数组第二个值





  private String pointerArrFullLen;//当前记录指针指向的数组的定义长度

  private String templeftarraynamelen="0";//记录数组名操作下标长度如a=a+1;得变成0+1；







  private  static List<Pair<String,String>> funLenList=new ArrayList<Pair<String,String>>();
  private  static List<String> leftfunarrlenList=new ArrayList<String>();
  public static List<Pair<String,String>> subTwoLens=new ArrayList<Pair<String,String>>();
  private static  List<Integer> sucnodenubs=new ArrayList<Integer>();
  private  static List<Boolean> funtwoarrflag=new ArrayList<Boolean>();




















  public static List<Boolean> getFuntwoarrflag() {
    return funtwoarrflag;
  }







  public static void setFuntwoarrflag(List<Boolean> pFuntwoarrflag) {
    funtwoarrflag = pFuntwoarrflag;
  }






  public String getFirstPointerGloLen() {
    return firstPointerGloLen;
  }






  public void setFirstPointerGloLen(String pFirstPointerGloLen) {
    firstPointerGloLen = pFirstPointerGloLen;
  }






  public String getSecondPointerGloLen() {
    return secondPointerGloLen;
  }






  public void setSecondPointerGloLen(String pSecondPointerGloLen) {
    secondPointerGloLen = pSecondPointerGloLen;
  }
  public static List<Pair<String, String>> getSubTwoLens() {
    return subTwoLens;
  }





  public static void setSubTwoLens(List<Pair<String, String>> pSubTwoLens) {
    subTwoLens = pSubTwoLens;
  }




  public int getFuncallnub() {
    return funcallnub;
  }




  public void setFuncallnub(int pFuncallnub) {
    funcallnub = pFuncallnub;
  }

  public static List<String> getLeftfunarrlenList() {
    return leftfunarrlenList;
  }



  public static void setLeftfunarrlenList(List<String> pLeftfunarrlenList) {
    leftfunarrlenList = pLeftfunarrlenList;
  }

  public String getTempleftarraynamelen() {
    return templeftarraynamelen;
  }


  public void setTempleftarraynamelen(String pTempleftarraynamelen) {
    templeftarraynamelen =templeftarraynamelen+"+("+pTempleftarraynamelen+")";
  }
  public void setTempleftarraynamelenZero(){
    this.templeftarraynamelen="0";
  }


  public static List<Integer> getSucnodenubs() {
    return sucnodenubs;
  }

  public static void setSucnodenubs(List<Integer> pSucnodenubs) {
    sucnodenubs = pSucnodenubs;
  }
  CRLGlobal(){

  }
  public static CRLGlobal getInstance() {
    if (instance == null) {
      instance = new CRLGlobal();
    }
    return instance;
  }
  public String getPointerArrFullLen() {
    return pointerArrFullLen;
  }

  public void setPointerArrFullLen(String pPointerArrFullLen) {
    pointerArrFullLen = pPointerArrFullLen;
  }

  public int getFunFlgLen() {
    return funFlgLen;
  }

  public void setFunFlgLen(int pFunFlgLen) {
    funFlgLen = pFunFlgLen;
  }
  public String getFunGloLen() {
    return funGloLen;
  }



  public String getPointerGloLen() {
    return pointerGloLen;
  }

  public void setPointerGloLen(String pPointerGloLen) {//具体计算指针下标运算========(p++)+(P--)等此种形式
    pointerGloLen =pointerGloLen+"+("+pPointerGloLen+")";
  }
  public void setPointerGloLenZero(){
    this.pointerGloLen="0";
  }






  public void setFunGloLen(String pFunGloLen) {
    funGloLen = pFunGloLen;
  }
  public static List<Pair<String, String>> getFunLenList() {
    return funLenList;
  }







  public static void setFunLenList(List<Pair<String, String>> pFunLenList) {
    funLenList = pFunLenList;
  }


}