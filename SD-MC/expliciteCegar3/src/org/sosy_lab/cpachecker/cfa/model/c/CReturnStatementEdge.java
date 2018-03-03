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

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CReturnStatement;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;

import com.google.common.base.Optional;

public class CReturnStatementEdge extends AbstractCFAEdge {

  private final CReturnStatement rawAST;

  public CReturnStatementEdge(String pRawStatement, CReturnStatement pRawAST,
      int pLineNumber, CFANode pPredecessor, FunctionExitNode pSuccessor) {

    super(pRawStatement, pLineNumber, pPredecessor, pSuccessor);
    rawAST = pRawAST;
  }

  @Override
  public CFAEdgeType getEdgeType() {
    return CFAEdgeType.ReturnStatementEdge;
  }

  public CExpression getExpression() {
    return rawAST.getReturnValue();
  }

  @Override
  public Optional<CReturnStatement> getRawAST() {
    return Optional.of(rawAST);
  }

  @Override
  public String getCode() {
    return rawAST.toASTString();
  }

  @Override
  public FunctionExitNode getSuccessor() {
    // the constructor enforces that the successor is always a FunctionExitNode
    return (FunctionExitNode)super.getSuccessor();
  }

  @Override
  public void setVars(Set<String> pSet) {
    // TODO Auto-generated method stub

  }

  @Override
  public List<String> getVars() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public boolean analysisCFAEdge(Stack<Map<String, Integer>> pStack, Map<String, Integer> pGlobal) {
    // TODO Auto-generated method stub
    return false;
  }
}