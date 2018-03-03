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

public final class CFieldReference extends CExpression {

  private final String         name;
  private final CExpression owner;
  private final boolean        isPointerDereference;

  public CFieldReference(final CFileLocation pFileLocation,
                            final CType pType,
                            final String pName,
                            final CExpression pOwner,
                            final boolean pIsPointerDereference) {
    super(pFileLocation, pType);
    name = pName;
    owner = pOwner;
    isPointerDereference = pIsPointerDereference;
  }

  public String getFieldName() {
    return name;
  }

  public CExpression getFieldOwner() {
    return owner;
  }

  public boolean isPointerDereference() {
    return isPointerDereference;
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
  public boolean judge(String var,boolean flag){
    if(owner instanceof CIdExpression){
      if(((CIdExpression) owner).getName().equals(var))
        return true;
    }
    return false;

  }
  @Override
  public String toASTString() {
    String left = (owner instanceof CFieldReference) ? owner.toASTString() : owner.toParenthesizedASTString();
    String op = isPointerDereference ? "->" : ".";
    return left + op  + name;
  }
  @Override
  public void setMyString(List<String> pList) {
    // TODO Auto-generated method stub
       pList.add(toASTString());
  }

  @Override
  public boolean varIsKnown(List<String> pUnknown,String func) {
    // TODO Auto-generated method stub
    return false;
  }
  @Override
  public void setVarName(List<String> list){
    if(isPointerDereference){
      list.add(name);
      owner.setVarName(list);
    }
    else{
      list.clear();
    }
  }

  @Override
  public void getKeyVars(){
     owner.getKeyVars();
  }

  @Override
  public void getInputVars(){
     owner.getKeyVars();
  }

}