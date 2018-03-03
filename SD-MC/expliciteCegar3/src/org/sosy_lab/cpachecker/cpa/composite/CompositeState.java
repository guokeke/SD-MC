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
package org.sosy_lab.cpachecker.cpa.composite;

import java.io.Serializable;
import java.util.Arrays;
import java.util.List;

import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractWrapperState;
import org.sosy_lab.cpachecker.core.interfaces.Partitionable;
import org.sosy_lab.cpachecker.core.interfaces.Targetable;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

public class CompositeState implements AbstractWrapperState, Targetable, Partitionable, Serializable {
  private static final long serialVersionUID = -5143296331663510680L;
  private final ImmutableList<AbstractState> states;
  private transient Object partitionKey; // lazily initialized
  public CompositeState(List<AbstractState> elements)
  {
    this.states = ImmutableList.copyOf(elements);
  }

  public int getNumberOfStates(){
    return states.size();
  }

  @Override
  public boolean isTarget() {
    for (AbstractState element : states) {
      if ((element instanceof Targetable) && ((Targetable)element).isTarget()) {
        return true;
      }
    }
    return false;
  }

  @Override
  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    builder.append('(');
    for (AbstractState element : states) {
      builder.append(element.getClass().getSimpleName());
      builder.append(": ");
      builder.append(element.toString());
      builder.append("\n ");
    }
    builder.replace(builder.length() - 1, builder.length(), ")");

    return builder.toString();
  }

  public AbstractState get(int idx) {
    return states.get(idx);
  }

  @Override
  public List<AbstractState> getWrappedStates() {
    return states;
  }


  @Override
  public Object getPartitionKey() {
    if (partitionKey == null) {
      Object[] keys = new Object[states.size()];

      int i = 0;
      for (AbstractState element : states) {
        if (element instanceof Partitionable) {
          keys[i] = ((Partitionable)element).getPartitionKey();
        }
        i++;
      }

      // wrap array of keys in object to enable overriding of equals and hashCode
      partitionKey = new CompositePartitionKey(keys);
    }

    return partitionKey;
  }

  private static final class CompositePartitionKey {

    private final Object[] keys;

    private CompositePartitionKey(Object[] pElements) {
      keys = pElements;
    }

    @Override
    public boolean equals(Object pObj) {
      if (this == pObj) {
        return true;
      }

      if (CompositePartitionKey.class != pObj.getClass()) {
        return false;
      }

      return Arrays.equals(this.keys, ((CompositePartitionKey)pObj).keys);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(keys);
    }

    @Override
    public String toString() {
      return "[" + Joiner.on(", ").skipNulls().join(keys) + "]";
    }
  }

  @Override
  public AbstractState getWrappedState() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public PathFormula getPathFormula() {
    // TODO Auto-generated method stub
    AbstractState second=states.get(2);
    if(second instanceof PredicateAbstractState){
      return ((PredicateAbstractState) second).getPathFormula();
    }
    return null;
  }

  @Override
  public void setNull() {
    // TODO Auto-generated method stub

  }


}