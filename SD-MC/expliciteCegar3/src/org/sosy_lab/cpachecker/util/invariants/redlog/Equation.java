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
package org.sosy_lab.cpachecker.util.invariants.redlog;

import org.sosy_lab.cpachecker.cfa.ast.c.CAstNode;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;

public class Equation {

  private String eqn;
  private CAstNode tree;

  public Equation() {}

  public Equation(String e) {
    eqn = e;
  }

  public void setFormula(String e) {
    eqn = e;
  }

  public void setTree(CAstNode t) {
    tree = t;
  }

  public CAstNode getTree() {
    return tree;
  }

  public String getRawSignature() {
    return eqn;
  }

  public CExpression getLeftHandSide() {
    CExpressionAssignmentStatement EAS =
      (CExpressionAssignmentStatement) tree;
    CExpression LHS = EAS.getLeftHandSide();
    return LHS;
  }

  public CExpression getRightHandSide() {
    CExpressionAssignmentStatement EAS =
      (CExpressionAssignmentStatement) tree;
    CExpression RHS = EAS.getRightHandSide();
    return RHS;
  }

}