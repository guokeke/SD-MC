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
package org.sosy_lab.cpachecker.cfa.model.c;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;

import com.google.common.base.Optional;

public class CDeclarationEdge extends AbstractCFAEdge {

  private final CDeclaration declaration;

  public CDeclarationEdge(final String pRawSignature, final int pLineNumber,
      final CFANode pPredecessor, final CFANode pSuccessor, final CDeclaration pDeclaration) {

    super(pRawSignature, pLineNumber, pPredecessor, pSuccessor);
    declaration = pDeclaration;
  }

  @Override
  public CFAEdgeType getEdgeType() {
    return CFAEdgeType.DeclarationEdge;
  }

  public CDeclaration getDeclaration() {
    return declaration;
  }

  @Override
  public Optional<CDeclaration> getRawAST() {
    return Optional.of(declaration);
  }

  @Override
  public String getCode() {
    return declaration.toASTString();
  }

  public void setDo(boolean pB) {
    // TODO Auto-generated method stub

  }
  @Override
  public void setVars(Set<String> set) {
    // TODO Auto-generated method stub
    list=new ArrayList<String>();
    list.addAll(set);
  }
  private List<String> list=null;

  @Override
  public List<String> getVars() {
    // TODO Auto-generated method stub
    return list;
  }
  public  String getDeclarationVar(){
    if(declaration instanceof CVariableDeclaration&&declaration.getName()!=null)
    return declaration.getName();
    return null;
  }
  @Override
  public boolean analysisCFAEdge(Stack<Map<String,Integer>> stack,Map<String,Integer> global) {
    // TODO Auto-generated method stub
    String varname=declaration.getName();
    if(varname!=null){
      Map<String,Integer> top = stack.peek();
     if(declaration.analysis(stack,global)){
      if(declaration.isGlobal()){
        global.put(varname,1);
      }
      else{
        top.put(varname, 1);
      }
     }
     else{
       if(declaration.isGlobal()){
         global.put(varname,0);
       }
       else{
         top.put(varname, 0);
       }
     }
    }
    return false;
}
}
