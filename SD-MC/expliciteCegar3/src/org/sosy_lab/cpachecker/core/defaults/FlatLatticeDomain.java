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

import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

/**
 * This class implements a domain for CPAs, where the partial order is
 * identical to the equality relation, if both of the two operands are neither
 * bottom nor top. The resulting lattice is a layered graph with three layers
 * (one for top, one for bottom and one for all other states) and edges only
 * between different layers.
 */
public class FlatLatticeDomain implements AbstractDomain {
  private final AbstractState mTopState;

  private static class TopState implements AbstractState {
    @Override
    public String toString() {
      return "<TOP>";
    }
    @Override
    public AbstractState getWrappedState() {
      // TODO Auto-generated method stub
      return null;
    }
    @Override
    public void setNull() {
      // TODO Auto-generated method stub

    }
  }

  public FlatLatticeDomain(AbstractState pTopState) {
    assert(pTopState != null);

    this.mTopState = pTopState;
  }

  public FlatLatticeDomain() {
    this(new TopState());
  }

  @Override
  public AbstractState join(AbstractState pState1, AbstractState pState2) throws CPAException {
    if (isLessOrEqual(pState1, pState2)) {
      return pState2;
    }

    if (isLessOrEqual(pState2, pState1)) {
      return pState1;
    }

    return mTopState;
  }

  @Override
  public boolean isLessOrEqual(AbstractState newState, AbstractState reachedState) throws CPAException {
    return (mTopState.equals(reachedState) || newState.equals(reachedState));
  }
}
