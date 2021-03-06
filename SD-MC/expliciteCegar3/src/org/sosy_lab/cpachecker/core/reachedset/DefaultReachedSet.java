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
package org.sosy_lab.cpachecker.core.reachedset;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.waitlist.Waitlist;
import org.sosy_lab.cpachecker.core.waitlist.Waitlist.WaitlistFactory;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.xidian.yk.Operators;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterators;

/**
 * Basic implementation of ReachedSet.
 * It does not group states by location or any other key.
 */
public class DefaultReachedSet implements ReachedSet {

  private final LinkedHashMap<AbstractState, Precision> reached;
  private Set<AbstractState> unmodifiableReached;
  private AbstractState lastState = null;
  private AbstractState firstState = null;
  private final Waitlist waitlist;
  private WaitlistFactory waitlistFactory;//mycode;
  private AbstractState noSucState=null;
  private Result result;
  private Pair<AbstractState,Precision> toChange=null;
  private Set<Pair<ARGState, ARGState>> highlightedEdges=new HashSet<Pair<ARGState, ARGState>>();
  public DefaultReachedSet(WaitlistFactory waitlistFactory) {
    reached = new LinkedHashMap<AbstractState, Precision>();
    unmodifiableReached = Collections.unmodifiableSet(reached.keySet());
    waitlist = waitlistFactory.createWaitlistInstance();
    this.waitlistFactory=waitlistFactory;//mycode
    result=Result.SAFE;
  }

  //mycode

  public WaitlistFactory getWaitlistFactory() {
    return waitlistFactory;
  }
  @Override
  public Result getResult() {
    return result;
  }

  @Override
  public void setResult(Result pResult) {
    result = pResult;
  }
  public void setWaitlistFactory(WaitlistFactory pWaitlistFactory) {
    waitlistFactory = pWaitlistFactory;
  }
  public void remove0(AbstractState state){
    reached.remove(state);
  }

  @Override
  public Pair<AbstractState, Precision> getToChange() {
    return toChange;
  }

  @Override
  public void setToChange(Pair<AbstractState, Precision> pToChange) {
    toChange = pToChange;
  }


  public Set<Pair<ARGState, ARGState>> getHighlightedEdges() {
    return highlightedEdges;
  }


  public void setHighlightedEdges(Set<Pair<ARGState, ARGState>> pHighlightedEdges) {
    highlightedEdges.addAll(pHighlightedEdges);
  }

  //mycode end
  @Override
  public void add(AbstractState state, Precision precision) throws IllegalArgumentException {
    Preconditions.checkNotNull(state);
    Preconditions.checkNotNull(precision);

    if (reached.size() == 0) {
      firstState = state;
    }
    Precision previousPrecision ;
     previousPrecision = reached.put(state, precision);
    if (previousPrecision == null) {
      // State wasn't already in the reached set.
      if(Operators.propertyIsTrue){
        Operators.myWaitStack.push(state);
      }
      else{
        waitlist.add(state);
      }
      lastState = state;

    } else {
      // State was already in the reached set.
      // This happens only if the MergeOperator produces a state that is already there.

      // The state may or may not be currently in the waitlist.
      // In the first case, we are not allowed to add it to the waitlist,
      // otherwise it would be in there twice (this method is responsible for
      // enforcing the set semantics of the waitlist).
      // In the second case, we do not need
      // to add it to the waitlist, because it was already handled
      // (we assume that the CPA would always produce the same successors if we
      // give it the same state twice).

      // So do nothing here.

      // But check if the new and the old precisions are equal.
      if (!precision.equals(previousPrecision)) {

        // Restore previous state of reached set
        // (a method shouldn't change state if it throws an IAE).
        reached.put(state, previousPrecision);

        throw new IllegalArgumentException("State added to reached set which is already contained, but with a different precision");
      }
    }
  }

  @Override
  public void addAll(Iterable<Pair<AbstractState, Precision>> toAdd) {
    for (Pair<AbstractState, Precision> pair : toAdd) {
      add(pair.getFirst(), pair.getSecond());
    }
  }

  @Override
  public void reAddToWaitlist(AbstractState s) {
    Preconditions.checkNotNull(s);
    Preconditions.checkArgument(reached.containsKey(s), "State has to be in the reached set");

    if (!waitlist.contains(s)) {
      waitlist.add(s);
    }
  }

  @Override
  public void updatePrecision(AbstractState s, Precision newPrecision) {
    Preconditions.checkNotNull(s);
    Preconditions.checkNotNull(newPrecision);

    Precision oldPrecision = reached.put(s, newPrecision);
    if (oldPrecision == null) {
      // State was not contained in the reached set.
      // Restore previous state and throw exception.
      reached.remove(s);
      throw new IllegalArgumentException("State needs to be in the reached set in order to change the precision.");
    }
  }

  @Override
  public void remove(AbstractState state) {
    Preconditions.checkNotNull(state);
    int hc = state.hashCode();
    if ((firstState == null) || hc == firstState.hashCode() && state.equals(firstState)) {
      firstState = null;
    }

    if ((lastState == null) || (hc == lastState.hashCode() && state.equals(lastState))) {
      lastState = null;
    }
    waitlist.remove(state);
    Precision precision=reached.get(state);
    reached.remove(state);
    precision=null;

  }

  @Override
  public void removeAll(Iterable<? extends AbstractState> toRemove) {
    for (AbstractState state : toRemove) {

      remove(state);
    }
    assert firstState != null || reached.isEmpty() : "firstState may only be removed if the whole reached set is cleared";
  }

  @Override
  public void removeOnlyFromWaitlist(AbstractState state) {
    checkNotNull(state);
    waitlist.remove(state);
  }

  @Override
  public void clear() {
    firstState = null;
    lastState = null;
    waitlist.clear();
    reached.clear();
  }

  @Override
  public Set<AbstractState> getReached() {
    return unmodifiableReached;
  }

  @Override
  public Iterator<AbstractState> iterator() {
    return unmodifiableReached.iterator();
  }

  @Override
  public Collection<Precision> getPrecisions() {
    return Collections.unmodifiableCollection(reached.values());
  }

  @Override
  public Collection<AbstractState> getReached(AbstractState state) {
    return getReached();
  }

  @Override
  public Collection<AbstractState> getReached(CFANode location) {
    return getReached();
  }

  @Override
  public AbstractState getFirstState() {
    Preconditions.checkState(firstState != null);
    return firstState;
  }

  @Override
  public AbstractState getLastState() {
    return lastState;
  }

  @Override
  public boolean hasWaitingState() {
    return !waitlist.isEmpty();
  }

  @Override
  public Collection<AbstractState> getWaitlist() {
    return new AbstractCollection<AbstractState>() {

      @Override
      public Iterator<AbstractState> iterator() {
        return Iterators.unmodifiableIterator(waitlist.iterator());
      }

      @Override
      public boolean contains(Object obj) {
        if (!(obj instanceof AbstractState)) {
          return false;
        }
        return waitlist.contains((AbstractState)obj);
      }

      @Override
      public boolean isEmpty() {
        return waitlist.isEmpty();
      }

      @Override
      public int size() {
        return waitlist.size();
      }

      @Override
      public String toString() {
        return waitlist.toString();
      }
    };
  }

  @Override
  public AbstractState popFromWaitlist() {
    return waitlist.pop();
  }

  @Override
  public int getWaitlistSize() {
    return waitlist.size();
  }

  @Override
  public Precision getPrecision(AbstractState state) {
    Preconditions.checkNotNull(state);
    Precision prec = reached.get(state);
    Preconditions.checkArgument(prec != null, "State not in reached set.");
    return prec;
  }

  @Override
  public boolean contains(AbstractState state) {
    Preconditions.checkNotNull(state);
    return reached.containsKey(state);
  }

  @Override
  public int size() {
    return reached.size();
  }

  @Override
  public boolean isEmpty() {
    return (size() == 0);
  }

  @Override
  public String toString() {
    return reached.keySet().toString();
  }
  public boolean safe=true;
  public Map<Integer, AbstractState> map = new HashMap<Integer,AbstractState>();
  @Override
  public AbstractState getNoSuc() {
    // TODO Auto-generated method stub
    return noSucState;
  }

  @Override
  public void setNoSuc(AbstractState s) {
    // TODO Auto-generated method stub
    if(noSucState==null){
      noSucState=s;
    }

  }
  @Override
  public void setLastState(ARGState pState) {
    // TODO Auto-generated method stub
    lastState=pState;
  }
}
