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
package org.sosy_lab.cpachecker.cfa.ast.c;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.cpachecker.cfa.types.c.CType;

/**
 * Super class for side-effect free expressions.
 */
public abstract class CExpression extends CRightHandSide {

  public CExpression(final CFileLocation pFileLocation,
                        final CType pType) {
    super(pFileLocation, pType);
  }

  public abstract <R, X extends Exception> R accept(CExpressionVisitor<R, X> v) throws X;

  public boolean judge(String pVar,boolean flag) {
    // TODO Auto-generated method stub
    return false;
  }
  public void setVarName(List<String> pListR){

  }
  public void extractImportantVars(Set<String> pSet, String pFunc) {
    // TODO Auto-generated method stub

  }

  public void setMyString(List<String> pList) {
    // TODO Auto-generated method stub

  }

  public abstract boolean varIsKnown(List<String> pUnknown,String func) ;
  public boolean analysis(Stack<Map<String,Integer>> stack,Map<String,Integer> global){return false;}

  public String getVarname() {
    // TODO Auto-generated method stub
    return null;
  }
  public boolean isGlobal(){
    return false;
  }

  public boolean hasKeyVar(){
    return false;
  }

  public void getKeyVars(){

  }

  public boolean hasInputVar(){
    return false;
  }

  public void getInputVars(){

  }
}
