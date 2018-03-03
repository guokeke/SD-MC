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

import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;

import com.google.common.base.Optional;

public class CStatementEdge extends AbstractCFAEdge {

  private final CStatement statement;

  public CStatementEdge(String pRawStatement, CStatement pStatement,
      int pLineNumber, CFANode pPredecessor, CFANode pSuccessor) {

    super(pRawStatement, pLineNumber, pPredecessor, pSuccessor);
    statement = pStatement;
  }

  @Override
  public CFAEdgeType getEdgeType() {
    return CFAEdgeType.StatementEdge;
  }

  public CStatement getStatement() {
    return statement;
  }

  @Override
  public Optional<CStatement> getRawAST() {
    return Optional.of(statement);
  }

  @Override
  public String getCode() {
    return statement.toASTString();
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

  @Override
  public boolean analysisCFAEdge(Stack<Map<String,Integer>> stack,Map<String,Integer> global) {
    // TODO Auto-generated method stub
    statement.analysisCFAEdge(stack, global);
    return false;
  }
  public String getLeft(){
    if(statement instanceof CFunctionCallAssignmentStatement)
      return ((CFunctionCallAssignmentStatement) statement).getLeft();
    return null;
  }
}