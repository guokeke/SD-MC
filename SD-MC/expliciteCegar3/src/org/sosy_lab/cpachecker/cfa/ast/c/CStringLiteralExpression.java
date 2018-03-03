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

import org.sosy_lab.cpachecker.cfa.types.c.CType;

public final class CStringLiteralExpression extends CLiteralExpression {

  private final String value;

  public CStringLiteralExpression(CFileLocation pFileLocation,
                                     CType pType,
                                     String pValue) {
    super(pFileLocation, pType);

    value = pValue;
  }

  @Override
  public String getValue() {
    return value;
  }

  @Override
  public <R, X extends Exception> R accept(CExpressionVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  @Override
  public <R, X extends Exception> R accept(CRightHandSideVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  @Override
  public String toASTString() {
    return value;
  }

  @Override
  public boolean varIsKnown(List<String> pUnknown, String pFunc) {
    // TODO Auto-generated method stub
    return false;
  }
  @Override
  public void setVarName(List<String> list){
    list.add(String.valueOf(value));
  }
}