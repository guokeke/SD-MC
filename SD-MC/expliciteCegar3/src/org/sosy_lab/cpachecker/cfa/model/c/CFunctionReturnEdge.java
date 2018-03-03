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

import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;

public class CFunctionReturnEdge extends AbstractCFAEdge {

  private final CFunctionSummaryEdge summaryEdge;

  public CFunctionReturnEdge(int pLineNumber,
      FunctionExitNode pPredecessor, CFANode pSuccessor,
      CFunctionSummaryEdge pSummaryEdge) {

    super("", pLineNumber, pPredecessor, pSuccessor);
    summaryEdge = pSummaryEdge;
  }

  public CFunctionSummaryEdge getSummaryEdge() {
    return summaryEdge;
  }

  @Override
  public String getCode() {
    return "";
  }

  @Override
  public String getDescription() {
    return "Return edge from " + getPredecessor().getFunctionName() + " to " + getSuccessor().getFunctionName();
  }

  @Override
  public CFAEdgeType getEdgeType() {
    return CFAEdgeType.FunctionReturnEdge;
  }

  @Override
  public FunctionExitNode getPredecessor() {
    // the constructor enforces that the predecessor is always a FunctionExitNode
    return (FunctionExitNode)super.getPredecessor();
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
