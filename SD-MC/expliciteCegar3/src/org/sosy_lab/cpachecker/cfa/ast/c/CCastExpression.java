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
import java.util.Set;

import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;

public final class CCastExpression extends CExpression {

  private final CExpression operand;
  private final CType     type;

  public CCastExpression(final CFileLocation pFileLocation,
                            final CType pExpressionType,
                            final CExpression pOperand,
                            final CType pType) {
    super(pFileLocation, pExpressionType);
    operand = pOperand;
    type = pType;
  }

  public CExpression getOperand() {
    return operand;
  }
  @Override
  public boolean judge(String pVar,boolean flag) {
    // TODO Auto-generated method stub
    if(type instanceof CPointerType&&operand instanceof CIdExpression){
      if(((CIdExpression) operand).judge1(pVar, true))
       return true;
    }
    else{
      if(operand.judge(pVar, flag))
        return true;
    }
     return false;

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

  @Override
  public String toASTString() {
    return "(" + type.toASTString("") + ")" + operand.toParenthesizedASTString();
  }
  @Override
  public void extractImportantVars(Set<String> set,String func){
         operand.extractImportantVars(set,func);
  }
  @Override
  public void setMyString(List<String> pList) {
    // TODO Auto-generated method stub
     operand.setMyString(pList);
  }

  @Override
  public boolean varIsKnown(List<String> pUnknown,String func) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public void getKeyVars(){
     operand.getKeyVars();
  }

  @Override
  public void getInputVars(){
     operand.getInputVars();
  }
}
