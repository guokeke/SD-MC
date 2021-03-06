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
import java.util.Stack;

import org.sosy_lab.cpachecker.cfa.types.c.CType;

public abstract class CLiteralExpression extends CExpression {

  public CLiteralExpression(final CFileLocation pFileLocation,
                               final CType pType) {
    super(pFileLocation, pType);
  }

  public abstract Object getValue();

  @Override
  protected String toParenthesizedASTString() {
    // literal expression never need parentheses
    return toASTString();
  }
  @Override
  public void setMyString(List<String> pList) {
    // TODO Auto-generated method stub
      // pList.add( toParenthesizedASTString());
  }
  @Override
  public boolean analysis(Stack<Map<String,Integer>> stack,Map<String,Integer> global){return true;}
}
