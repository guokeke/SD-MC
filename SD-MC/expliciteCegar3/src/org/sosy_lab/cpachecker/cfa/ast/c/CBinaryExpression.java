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

public class CBinaryExpression extends CExpression {

  private final CExpression operand1;
  private final CExpression operand2;
  private final BinaryOperator operator;

  public CBinaryExpression(final CFileLocation pFileLocation,
                              final CType pType,
                              final CExpression pOperand1,
                              final CExpression pOperand2,
                              final BinaryOperator pOperator) {
    super(pFileLocation, pType);
    operand1 = pOperand1;
    operand2 = pOperand2;
    operator = pOperator;
  }

  public CExpression getOperand1() {
    return operand1;
  }

  public CExpression getOperand2() {
    return operand2;
  }

  public BinaryOperator getOperator() {
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

  @Override
  public String toASTString() {
    return operand1.toParenthesizedASTString() + " "
        + operator.getOperator() + " " + operand2.toParenthesizedASTString();
  }
  @Override
  public boolean judge(String var,boolean flag){
    if((operand1 instanceof CUnaryExpression)||(operand1 instanceof CFieldReference)
        ||(operand1 instanceof CBinaryExpression)){
      if(operand1.judge(var,flag)){
         return true;
      }
    }
    if(operand1 instanceof CIdExpression){
         String name=((CIdExpression) operand1).getName();
         CType type=operand1.getExpressionType();
         if(type instanceof CPointerType && name.equals(var)&&flag)
           return true;
    }
    if(operand2 instanceof CIdExpression){
      String name=((CIdExpression) operand2).getName();
      CType type=operand2.getExpressionType();
      if(type instanceof CPointerType && name.equals(var)&&flag)
        return true;
    }
    if((operand2 instanceof CUnaryExpression)||(operand2 instanceof CFieldReference)
        ||(operand2 instanceof CBinaryExpression)){
      if(operand2.judge(var,flag)){
         return true;
      }
    }
    return false;
  }
  public static enum BinaryOperator {
    MULTIPLY      ("*"),
    DIVIDE        ("/"),
    MODULO        ("%"),
    PLUS          ("+"),
    MINUS         ("-"),
    SHIFT_LEFT    ("<<"),
    SHIFT_RIGHT   (">>"),
    LESS_THAN     ("<"),
    GREATER_THAN  (">"),
    LESS_EQUAL    ("<="),
    GREATER_EQUAL (">="),
    BINARY_AND    ("&"),
    BINARY_XOR    ("^"),
    BINARY_OR     ("|"),
    LOGICAL_AND   ("&&"),
    LOGICAL_OR    ("||"),
    EQUALS        ("=="),
    NOT_EQUALS    ("!="),
    ;

    private final String op;

    private BinaryOperator(String pOp) {
      op = pOp;
    }

    /**
     * Returns the string representation of this operator (e.g. "*", "+").
     */
    public String getOperator() {
      return op;
    }
  }
  @Override
  public boolean varIsKnown(List<String> pUnknown,String func) {
    // TODO Auto-generated method stub
    if(operand1.varIsKnown(pUnknown,func))
      return true;
    else
      return operand2.varIsKnown(pUnknown,func);
  }
  @Override
  public boolean analysis(Stack<Map<String,Integer>> stack,Map<String,Integer> global){

    return operand1.analysis(stack, global)&&operand2.analysis(stack, global);
  }

  @Override
  public boolean hasKeyVar(){
    if(operand1.hasKeyVar() || operand2.hasKeyVar()){//目前没有函数名
       return true;
    }

    return false;
  }

  @Override
  public void getKeyVars(){
     operand1.getKeyVars();
     operand2.getKeyVars();
  }


  @Override
  public boolean hasInputVar(){
    if(operand1.hasInputVar() || operand2.hasInputVar()){//目前没有函数名
       return true;
    }

    return false;
  }

  @Override
  public void getInputVars(){
     operand1.getInputVars();
     operand2.getInputVars();
  }
}
