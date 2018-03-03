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
package org.sosy_lab.cpachecker.core.defaults;

import java.io.Serializable;
import java.util.Collections;

import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractWrapperState;
import org.sosy_lab.cpachecker.core.interfaces.Partitionable;
import org.sosy_lab.cpachecker.core.interfaces.Targetable;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;

/**
 * Base class for AbstractStates which wrap the abstract state of exactly
 * one CPA.
 */
public abstract class AbstractSingleWrapperState implements AbstractWrapperState, Targetable, Partitionable, Serializable {

  private static final long serialVersionUID = -332757795984736107L;
  private static Function<AbstractState, AbstractState> unwrapFunction
      = new Function<AbstractState, AbstractState>() {

    @Override
    public AbstractState apply(AbstractState pArg0) {//see
      Preconditions.checkArgument(pArg0 instanceof AbstractSingleWrapperState);

      return ((AbstractSingleWrapperState)pArg0).getWrappedState();
    }
  };

  public static Function<AbstractState, AbstractState> getUnwrapFunction() {
    return unwrapFunction;
  }

  private AbstractState wrappedState;//修改了，把final去掉了
  //mycode
  //mycodeend
  public AbstractSingleWrapperState(AbstractState pWrappedState) {
    // TODO this collides with some CPAs' way of handling TOP and BOTTOM, but it should really be not null here
    // Preconditions.checkNotNull(pWrappedState);
    wrappedState = pWrappedState;
  }

  @Override
  public AbstractState getWrappedState() {
    return wrappedState;
  }
  //mycode
  public void setWrappedState(AbstractState wrapped) {
     wrappedState=wrapped;
  }
  //mycode end
  @Override
  public boolean isTarget() {
    if (wrappedState instanceof Targetable) {
      return ((Targetable)wrappedState).isTarget();
    } else {
      return false;
    }
  }

  @Override
  public Object getPartitionKey() {
    if (wrappedState instanceof Partitionable) {
      return ((Partitionable)wrappedState).getPartitionKey();
    } else {
      return null;
    }
  }

  @Override
  public String toString() {
    return wrappedState.toString();
  }

  @Override
  public Iterable<? extends AbstractState> getWrappedStates() {
    return Collections.singleton(wrappedState);
  }
  //mycode
  /*
  @Override
  public CFANode getCFANode(){
    return loc;
  }
  public void setCFANode(){
    loc=AbstractStates.extractLocation(this);
  }
  public boolean isLocEqual(ARGState argState){
    return loc.getNodeNumber()==argState.getCFANode().getNodeNumber();
  }
  */
  @Override
  public abstract PathFormula getPathFormula();
  //mycodeend

  @Override
  public void setNull() {
    // TODO Auto-generated method stub
    //unwrapFunction=null;
    wrappedState=null;
  }
}
