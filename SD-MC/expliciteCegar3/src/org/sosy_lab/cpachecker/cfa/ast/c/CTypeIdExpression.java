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

public final class CTypeIdExpression extends CExpression {

  private final TypeIdOperator operator;
  private final CType type;

  public CTypeIdExpression(final CFileLocation pFileLocation,
                              final CType pExpressionType, final TypeIdOperator pOperator,
                              final CType pType) {
    super(pFileLocation, pExpressionType);
    operator = pOperator;
    type = pType;
  }

  public TypeIdOperator getOperator() {
    return operator;
  }

  public CType getType() {
    return type;
  }

  @Override
  public <R, X extends Exception> R accept(CExpressionVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  @Override
  public <R, X extends Exception> R accept(CRightHandSideVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  public enum TypeIdOperator {
    SIZEOF,
    TYPEID,
    ALIGNOF,
    TYPEOF,
    ;

    /**
     * Returns the string representation of this operator
     */
    public String getOperator() {
      return toString().toLowerCase();
    }
  }

  @Override
  public String toASTString() {
    return operator.getOperator() + "(" + type.toASTString("") + ")";
  }

  @Override
  public boolean varIsKnown(List<String> pUnknown, String pFunc) {
    // TODO Auto-generated method stub
    return false;
  }
}
