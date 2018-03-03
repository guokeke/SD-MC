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
import org.xidian.yk.KeyVar;
import org.xidian.yk.Operators;

public final class CIdExpression extends CExpression {

  private final String name;
  private final CSimpleDeclaration declaration;

  public CIdExpression(final CFileLocation pFileLocation,
                          final CType pType, final String pName,
                          final CSimpleDeclaration pDeclaration) {
    super(pFileLocation, pType);
    name = pName.intern();
    declaration = pDeclaration;
  }

  public String getName() {
    return name;
  }

  /**
   * Get the declaration of the variable.
   * The result may be null if the variable was not declared.
   */
  public CSimpleDeclaration getDeclaration() {
    return declaration;
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
    return name;
  }

  @Override
  protected String toParenthesizedASTString() {
    // id expression never need parentheses
    return toASTString();
  }
  @Override
  public void setMyString(List<String> pList) {
    // TODO Auto-generated method stub
      // pList.add(name);
  }

  @Override
  public boolean varIsKnown(List<String> pUnknown,String func) {
    // TODO Auto-generated method stub
    if(declaration instanceof CVariableDeclaration){
      if(((CVariableDeclaration) declaration).isGlobal())
        func="global";
    }
    if(pUnknown.contains(func+"::"+name))
      return true;
    return false;
  }
  @Override
  public boolean judge(String var,boolean f){
    if(f&&var.equals(name)&&super.getExpressionType() instanceof CPointerType)
      return true;
    return false;
  }
  public boolean judge1(String var,boolean f){
    if(f&&var.equals(name))
      return true;
    return false;
  }
  @Override
  public boolean analysis(Stack<Map<String,Integer>> stack,Map<String,Integer> global){
    Map<String,Integer> top=stack.peek();
    if(declaration.analysis(stack,global))
     return  declaration.analysis(stack,global);
    else{
      if(top.get(name)==1||global.keySet().contains(name))
        return true;
      else
        return false;
    }
  }
  @Override
  public String getVarname(){
    return name;
  }
  @Override
  public boolean isGlobal(){
    if(declaration instanceof CDeclaration){
      return ((CDeclaration) declaration).isGlobal();
    }
    return false;
  }
  @Override
  public void setVarName(List<String> list){
        list.add(name);
  }

  @Override
  public boolean hasKeyVar(){
    if(KeyVar.keyVarSet.contains(name)){//目前没有函数名
       return true;
    }
    return false;
  }

  @Override
  public void getKeyVars(){
    KeyVar.keyVarSet.add(name);
  }

  @Override
  public boolean hasInputVar(){
    if(Operators.inputOrRandVar.contains(name)){//目前没有函数名
       return true;
    }
    return false;
  }

  @Override
  public void getInputVars(){
    Operators.inputOrRandVar.add(name);
  }
}
