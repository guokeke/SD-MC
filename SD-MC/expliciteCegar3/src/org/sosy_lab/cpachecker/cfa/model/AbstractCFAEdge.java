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
package org.sosy_lab.cpachecker.cfa.model;


import com.google.common.base.Optional;
import com.google.common.base.Preconditions;

public abstract class AbstractCFAEdge implements CFAEdge {

  private CFANode predecessor;
  private CFANode successor;
  private final String rawStatement;
  private final int lineNumber;
  private boolean isKeyEdge=false;
  private boolean isInputEdge=false;
  private boolean notTrans=false;

  public AbstractCFAEdge(String pRawStatement, int pLineNumber,
      CFANode pPredecessor, CFANode pSuccessor) {

    Preconditions.checkNotNull(pRawStatement);
    Preconditions.checkNotNull(pPredecessor);
    Preconditions.checkNotNull(pSuccessor);

    predecessor = pPredecessor;
    successor = pSuccessor;
    rawStatement = pRawStatement;
    lineNumber = pLineNumber;
  }


  @Override
  public boolean isKeyEdge() {
    return isKeyEdge;
  }


  @Override
  public void setKeyEdge(boolean pIsKeyEdge) {
    isKeyEdge = pIsKeyEdge;
  }

  @Override
  public CFANode getPredecessor() {
    return predecessor;
  }
  @Override
  public void setPredecessor(CFANode pre){
    predecessor=pre;
  }
  @Override
  public CFANode getSuccessor() {
    return successor;
  }
  @Override
  public void setSuccessor(CFANode suc){
    successor=suc;
  }
  @Override
  public String getRawStatement() {
    return rawStatement;
  }

  @Override
  public Optional<?> getRawAST() {
    return Optional.absent();
  }

  @Override
  public String getDescription() {
    return getCode();
  }

  @Override
  public int getLineNumber() {
    return lineNumber;
  }

  @Override
  public int hashCode() {
    return 31 * predecessor.hashCode() + successor.hashCode();
  }

  @Override
  public boolean equals(Object pOther) {
    if (!(pOther instanceof AbstractCFAEdge)) {
      return false;
    }

    AbstractCFAEdge otherEdge = (AbstractCFAEdge) pOther;

    if ((otherEdge.predecessor != predecessor)
        || (otherEdge.successor != successor)) {
      return false;
    }

    return true;
  }

  @Override
  public String toString() {
    return "Line " + getLineNumber() + ":\t" + getPredecessor() + " -{" +
        getDescription().replaceAll("\n", " ") +
        "}-> " + getSuccessor();
  }


  @Override
  public boolean isInputEdge() {
    return isInputEdge;
  }


  @Override
  public void setInputEdge(boolean pIsInputEdge) {
    isInputEdge = pIsInputEdge;
  }

  @Override
  public void setNotTrans(boolean pNotTrans) {
    notTrans = pNotTrans;
  }

  @Override
  public boolean getNotTrans() {
    return notTrans;
  }
}
