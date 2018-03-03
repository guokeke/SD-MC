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

import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;

public class CUnaryExpression extends CExpression {

  private final CExpression operand;
  private final UnaryOperator  operator;

  public CUnaryExpression(final CFileLocation pFileLocation,
                             final CType pType, final CExpression pOperand,
                             final UnaryOperator pOperator) {
    super(pFileLocation, pType);
    operand = pOperand;
    operator = pOperator;
  }

  public CExpression getOperand() {
    return operand;
  }

  public UnaryOperator getOperator() {
    return operator;
  }

  @Override
  public <R, X extends Exception> R accept(CExpressionVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  @Override
  public <R, X extends Exception> R accept(CRightHandSideVisitor<R, X> v) throws X {
    return v.visit(this);
  }

  public static enum UnaryOperator {
    PLUS   ("+"),
    MINUS  ("-"),
    STAR   ("*"),
    AMPER  ("&"),
    TILDE  ("~"),
    NOT    ("!"),
    SIZEOF ("sizeof"),
    ;

    private final String mOp;

    private UnaryOperator(String pOp) {
      mOp = pOp;
    }

    /**
     * Returns the string representation of this operator (e.g. "*", "+").
     */
    public String getOperator() {
      return mOp;
    }
  }
  @Override
  public boolean judge(String var,boolean flag){
    if(operator.mOp.equals("*"))
      flag=true;
    if((operand instanceof CUnaryExpression)||(operand instanceof CFieldReference)
        ||(operand instanceof CBinaryExpression)||(operand instanceof CCastExpression)){
      if(operand.judge(var,flag)){
         return true;
      }
    }
    if(operand instanceof CIdExpression){
      if(!operator.getOperator().equals("*"))
        return false;
         String name=((CIdExpression) operand).getName();
         CType type=operand.getExpressionType();
         if(type instanceof CPointerType && name.equals(var))
           return true;
    }
    return false;

  }
  @Override
  public String toASTString() {
    if (operator == UnaryOperator.SIZEOF) {
      return operator.getOperator() + "(" + operand.toASTString() + ")";
    } else {
      return operator.getOperator() + operand.toParenthesizedASTString();
    }
  }
  @Override
  public void setVarName(List<String> list){
      operand.setVarName(list);
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
  public boolean analysis(Stack<Map<String,Integer>> stack,Map<String,Integer> global){

    return operand.analysis(stack, global);
  }
  @Override
  public String getVarname(){
    return operand.getVarname();
  }

  @Override
  public boolean hasKeyVar(){
    return operand.hasKeyVar();
  }

  @Override
  public void getKeyVars(){
     operand.getKeyVars();
  }

  @Override
  public boolean hasInputVar(){
    return operand.hasKeyVar();
  }

  @Override
  public void getInputVars(){
     operand.getKeyVars();
  }
}
