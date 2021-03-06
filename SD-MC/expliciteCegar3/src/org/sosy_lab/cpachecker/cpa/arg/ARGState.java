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
package org.sosy_lab.cpachecker.cpa.arg;

import static com.google.common.base.Preconditions.*;
import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.defaults.AbstractSingleWrapperState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.base.Function;
import com.google.common.collect.Iterables;
import com.google.common.primitives.Ints;
import com.songstan.ltl_trans.method.Transition;

import de.uni_freiburg.informatik.ultimate.logic.Term;
public class ARGState extends AbstractSingleWrapperState implements Comparable<ARGState> {

  private static final long serialVersionUID = 2608287648397165040L;
  private Set<ARGState> children;
  private Set<ARGState> parents; // more than one parent if joining elements

  private ARGState mCoveredBy = null;
  private Set<ARGState> mCoveredByThis = null; // lazy initialization because rarely needed

  // boolean which keeps track of which elements have already had their successors computed
  private boolean wasExpanded = false;
  private boolean mayCover = true;
  private boolean destroyed = false;

  private ARGState mergedWith = null;

  private final int stateId;
  //public PathFormula addPathFormula=null;
  private static int nextArgStateId = 0;
  //mycode
  private Proposition proposition;
  private String properties;
  private Transition transition;
  private List<Integer> util;
  private List<Integer> flag=new ArrayList<Integer>();
  private boolean unknown=false;//求覆盖时使用   True:遇到分支，判断不出该走哪一条; false,能判断出
  private boolean isFalse=false;//判断是否可达
 // private boolean notCovered=false;
  private boolean target=false;
  private int level=0;
  private List<Formula> formulas=new ArrayList<Formula>();
  private CFANode loc=null;
  private Map<String, Term> lastTerms=null;


  public Map<String, Term> getLastTerms() {
    return lastTerms;
  }

  public void setLastTerms(Map<String, Term> pLastTerms) {
    lastTerms = new HashMap<String, Term>();
    lastTerms.putAll(pLastTerms);
  }

  public String getRangeOfInputVars() {
    return rangeOfInputVars;
  }



  public void setRangeOfInputVars(String pRangeOfInputVars) {
    rangeOfInputVars = pRangeOfInputVars;
  }


  private boolean varIsNull=true;
  private Map<String, String> valuesOfKeyVariables=new HashMap<String, String>();//yangkai
  private String rangeOfInputVars="";//记录当前路径上输入变量的范围

  public Map<String, String> getValuesOfKeyVariables() {
    return valuesOfKeyVariables;
  }


  public void setValuesOfKeyVariables(Map<String, String> pValuesOfKeyVariables) {
    valuesOfKeyVariables.putAll(pValuesOfKeyVariables);
  }


  //<yangkai> 路径公式
  private List<Formula> keyFormulas=new ArrayList<Formula>();

  public boolean hasCompute=false;
  public boolean hasUpdate=false;
  public String callstack="";
 // public List<Formula> tempFormulas=null;
  //public Map<String, Map<String, Integer>> newMap = new HashMap<String, Map<String, Integer>>();
  //public Map<String, Integer> varsInfo = new HashMap<String, Integer>();
  public Stack<Pair<Map<String, Map<String, Integer>>,Map<String, Integer>>> stack =null;
                                      // new Stack<Pair<Map<String, Map<String, Integer>>,Map<String, Integer>>>();
////mycode end
  private String model="";
  public ARGState(AbstractState pWrappedState, ARGState pParentElement) {
    super(pWrappedState);
    stateId = ++nextArgStateId;
    parents = new LinkedHashSet<ARGState>(1); // TODO Is HashSet enough? It would be more memory-efficient.
    if (pParentElement != null){
      addParent(pParentElement);
    }
    children = new LinkedHashSet<ARGState>(1);
    proposition=new Proposition();
    properties="";
    transition=new Transition("","","");
    util=new ArrayList<Integer>();
  }

  public void clear(){
    children.clear();
    parents.clear();
  }
  @Override
  public void setNull(){
    super.setNull();
    proposition=null;
    parents=null;
    formulas=null;
    stack=null;
    children=null;
    transition=null;
    util=null;
    flag=null;
    mCoveredByThis=null;
    mCoveredBy=null;
    loc=null;
    properties=null;
    callstack=null;

  }

//  public boolean isNotCovered() {
//    return notCovered;
//  }
//
//
//  public void setNotCovered(boolean pNotCovered) {
//    notCovered = pNotCovered;
//  }


  public Transition getTransition() {
    return transition;
  }


  public void setTransition(Transition pTransition) {
    transition = pTransition;
  }

  public boolean isVarIsNull() {
    return varIsNull;
  }



  public void setVarIsNull(boolean pVarIsNull) {
    varIsNull = pVarIsNull;
  }


  public CFANode getLoc() {
    return loc;
  }


  public void setLoc(CFANode pLoc) {
    loc = pLoc;
  }

  public List<Integer> getFlag() {
    return flag;
  }
  public void setFlag(List<Integer> pFlag) {
    flag = pFlag;
  }
  public List<Integer> getUtil() {
    return util;
  }
  public void setUtil(List<Integer> pUtil) {
    util = pUtil;
  }
  public List<Formula> getFormulas() {
    return formulas;
  }
  public void setForlumas(List<Formula> pFormulas) {
    if(pFormulas==null)
      formulas=null;
    else
      formulas = new ArrayList<Formula>(pFormulas);
  }
  public int getLevel() {
    return level;
  }
  public void setLevel(int pLevel) {
    level = pLevel;
  }
  public Proposition getProposition(){
     return proposition;
  }
  public void setProposition(Proposition p){
    proposition=p;
  }
  public void setProposition(){
    proposition=null;
  }
  public void setProposition(String s){
    proposition=new Proposition(s);
  }
  public String getProperties() {
    return properties;
  }

  public void setProperties(String properties) {
    this.properties = properties;
  }

  public boolean isMyTarget() {
    return target;
  }
  public void setMyTarget(boolean pTarget) {
    target = pTarget;
  }
  //mycodeend
  public Set<ARGState> getParents(){
    // TODO return unmodifiable view?
    return parents;
  }
  public void addParent(ARGState pOtherParent){
    assert !destroyed : "Don't use destroyed ARGState " + this;
  if(stateId==73){
    int i=1;
    i=i+1;
  }
    if (parents.add(pOtherParent)){
      pOtherParent.children.add(this);
    }
  }
  public Set<ARGState> getChildren() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    return children;
  }
  public void setCovered(ARGState pCoveredBy) {
    checkState(!isCovered(), "Cannot cover already covered element %s", this);
    checkNotNull(pCoveredBy);//see
    checkArgument(pCoveredBy.mayCover, "Trying to cover with non-covering element %s", pCoveredBy);
    mCoveredBy = pCoveredBy;
    if (pCoveredBy.mCoveredByThis == null) {
      // lazy initialization because rarely needed
      pCoveredBy.mCoveredByThis = new HashSet<ARGState>(2);
    }
    pCoveredBy.mCoveredByThis.add(this);
  }
  public void uncover() {
    assert isCovered();
    assert mCoveredBy.mCoveredByThis.contains(this);
    mCoveredBy.mCoveredByThis.remove(this);
    mCoveredBy = null;
  }
  public boolean isCovered() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    return mCoveredBy != null;
  }
  public ARGState getCoveringState() {
    checkState(isCovered());
    return mCoveredBy;
  }
  public Set<ARGState> getCoveredByThis() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    if (mCoveredByThis == null) {
      return Collections.emptySet();
    } else {
      return Collections.unmodifiableSet(mCoveredByThis);
    }
  }
  protected void setMergedWith(ARGState pMergedWith) {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    assert mergedWith == null : "Second merging of element " + this;

    mergedWith = pMergedWith;
  }
  protected ARGState getMergedWith() {
    return mergedWith;
  }
  public boolean mayCover() {
    return mayCover && !isCovered();
  }

  public void setNotCovering() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    mayCover = false;
  }

  public void setCovering() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    mayCover = true;
  }

  public boolean wasExpanded() {
    return wasExpanded;
  }

  void markExpanded() {
    wasExpanded = true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    if (destroyed) {
      sb.append("Destroyed ");
    }
    if (mCoveredBy != null) {
      sb.append("Covered ");
    }
    sb.append("ARG State (Id: ");
    sb.append(stateId);
    if (!destroyed) {
      sb.append(", Parents: ");
      sb.append(stateIdsOf(parents));
      sb.append(", Children: ");
      sb.append(stateIdsOf(children));

      if (mCoveredBy != null) {
        sb.append(", Covered by: ");
        sb.append(mCoveredBy.stateId);
      } else {
        sb.append(", Covering: ");
        sb.append(stateIdsOf(getCoveredByThis()));
      }
    }
    sb.append(") ");
    sb.append(getWrappedState());//see
    return sb.toString();
  }

  private final Iterable<Integer> stateIdsOf(Iterable<ARGState> elements) {
    return Iterables.transform(elements, new Function<ARGState, Integer>() {
      @Override
      public Integer apply(ARGState pInput) {
        return pInput.stateId;
      }
    });
  }

  // TODO check
  public Set<ARGState> getSubgraph() {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    Set<ARGState> result = new HashSet<ARGState>();
    Deque<ARGState> workList = new ArrayDeque<ARGState>();

    workList.add(this);
    while (!workList.isEmpty()) {
      ARGState currentElement = workList.removeFirst();
      if (result.add(currentElement)) {
        // currentElement was not in result
        workList.addAll(currentElement.children);
      }
    }
    return result;
  }
  public Set<ARGState> removeSubgraph(ReachedSet reachedSet,ARGState state) {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    Set<ARGState> result = new HashSet<ARGState>();
    Deque<ARGState> workList = new ArrayDeque<ARGState>();

    workList.add(this);
    int i=1;
//    if(MyInfo.current==-1){
//      MyInfo.current=this.getStateId();
//      Set<ARGState> set=new HashSet<ARGState>();
//      MyInfo.possibleRemoves.put(MyInfo.current,set);
//    }
//    else{
//      if(MyInfo.current!=this.getStateId()){
//      MyInfo.possibleRemoves.put(this.getStateId(),MyInfo.possibleRemoves.get(MyInfo.current));
//
//       MyInfo.possibleRemoves.remove(MyInfo.current);
//      MyInfo.current=this.getStateId();
//      }
//    }
    while (!workList.isEmpty()) {
      ARGState currentElement = workList.removeFirst();
      if (result.add(currentElement)) {
        // currentElement was not in result
        workList.addAll(currentElement.children);
      }


      if(currentElement==this||currentElement==state)
        continue;
      if(reachedSet.getWaitlist().contains(currentElement)){
        continue;
      }
      else if(!currentElement.hasCompute){
        continue;
      }
      else if(currentElement.isCovered()){
        continue;
      }
      else{
        if(currentElement.getLoc()!=null){
          if(currentElement.getLoc().getNumEnteringEdges()>1){
            currentElement.removeChildren();
            //MyInfo.possibleRemoves.get(this.getStateId()).add(currentElement);
            continue;
          }
          else if(currentElement.getLoc().isLoopStart()){
            currentElement.removeChildren();
           // MyInfo.possibleRemoves.get(this.getStateId()).add(currentElement);
            continue;
          }
        }
        currentElement.removeFromARG();
        reachedSet.remove(currentElement);
       // currentElement.removeFromARG();
        System.out.println("#"+currentElement.getStateId());
        //next.clear();
       // next.setNull();
        currentElement=null;
      }
    }
    return result;
  }

  private void removeChildren() {
    // TODO Auto-generated method stub
    assert !destroyed : "Don't use destroyed ARGState " + this;
  // clear children
  for (ARGState child : children) {
    assert (child.parents.contains(this));
    child.parents.remove(this);
    //child.setDestroyed(true);
  }
  children.clear();
  // clear coverage relation

  }

  /**
   * This method removes this element from the ARG by removing it from its
   * parents' children list and from its children's parents list.
   *
   * This method also removes the element from the covered set of the other
   * element covering this element, if it is covered.
   *
   * This means, if its children do not have any other parents, they will be not
   * reachable any more, i.e. they do not belong to the ARG any more. But those
   * elements will not be removed from the covered set.
   */
  public void removeFromARG() {
    assert !destroyed : "Don't use destroyed ARGState " + this;

    // clear children
    for (ARGState child : children) {
      assert (child.parents.contains(this));
      child.parents.remove(this);
      //child.setDestroyed(true);
    }
    children.clear();

    // clear parents
    for (ARGState parent : parents) {
      assert (parent.children.contains(this));
      parent.children.remove(this);
    }
    parents.clear();

    // clear coverage relation
    if (isCovered()) {
      assert mCoveredBy.mCoveredByThis.contains(this);

      mCoveredBy.mCoveredByThis.remove(this);
      mCoveredBy = null;
    }

    if (mCoveredByThis != null) {
      for (ARGState covered : mCoveredByThis) {
        covered.mCoveredBy = null;
      }
      mCoveredByThis.clear();
      mCoveredByThis = null;
    }

    destroyed = true;
  }

  /**
   * This method does basically the same as removeFromARG for this element, but
   * before destroying it, it will copy all relationships to other elements to
   * a new state. I.e., the replacement element will receive all parents and
   * children of this element, and it will also cover all elements which are
   * currently covered by this element.
   *
   * @param replacement
   */
  protected void replaceInARGWith(ARGState replacement) {
    assert !destroyed : "Don't use destroyed ARGState " + this;
    assert !replacement.destroyed : "Don't use destroyed ARGState " + replacement;
    assert !isCovered() : "Not implemented: Replacement of covered element " + this;
    assert !replacement.isCovered() : "Cannot replace with covered element " + replacement;

    // copy children
    for (ARGState child : children) {
      assert (child.parents.contains(this)) : "Inconsistent ARG at " + this;
      child.parents.remove(this);
      child.addParent(replacement);
    }
    children.clear();

    for (ARGState parent : parents) {
      assert (parent.children.contains(this)) : "Inconsistent ARG at " + this;
      parent.children.remove(this);
      replacement.addParent(parent);
    }
    parents.clear();

    if (mCoveredByThis != null) {
      if (replacement.mCoveredByThis == null) {
        // lazy initialization because rarely needed
        replacement.mCoveredByThis = new HashSet<ARGState>(mCoveredByThis.size());
      }

      for (ARGState covered : mCoveredByThis) {
        assert covered.mCoveredBy == this : "Inconsistent coverage relation at " + this;
        covered.mCoveredBy = replacement;
        replacement.mCoveredByThis.add(covered);
      }

      mCoveredByThis.clear();
      mCoveredByThis = null;
    }

    destroyed = true;
  }

  public int getStateId() {
    return stateId;
  }

  public CFAEdge getEdgeToChild(ARGState pChild) {
    checkNotNull(children);
    checkArgument(children.contains(pChild));

    CFANode currentLoc = extractLocation(this);
    CFANode childNode = extractLocation(pChild);

    return currentLoc.getEdgeTo(childNode);
  }

  public boolean isDestroyed() {
    return destroyed;
  }
  public void setDestroyed(boolean b) {
     destroyed=b;
  }
  /**
   * The ordering of this class is the chronological creation order.
   *
   * Note: Although equals() is not overwritten, this ordering is consistent
   * with equals() as the stateId field is unique.
   */
  @Override
  public int compareTo(ARGState pO) {
    return Ints.compare(this.stateId, pO.stateId);
  }

  public boolean isOlderThan(ARGState other) {
    return (stateId < other.stateId);
  }
  @Override
  public PathFormula getPathFormula() {
    // TODO Auto-generated method stub
    return ((AbstractSingleWrapperState) getWrappedState()).getPathFormula();
  }
  public String propertiesToString(){
    StringBuilder builder=new StringBuilder();
    builder.append("properties{ ");
    if(properties.equals("")){
      builder.append("null }");
      return builder.toString();
    }
    builder.append(properties);
    builder.append("}");
    return builder.toString();
  }

  public boolean isUnknown() {
    return unknown;
  }

  public void setUnknown(boolean pUnknown) {
    unknown = pUnknown;
  }

  public boolean isFalse() {
    return isFalse;
  }

  public void setFalse(boolean b){
     isFalse=b;
  }
  public void copyVarInfos(Stack<Pair<Map<String, Map<String, Integer>>,Map<String, Integer>>> stack1){
    if(stack1==null){
      stack=new Stack<Pair<Map<String, Map<String, Integer>>,Map<String, Integer>>>();
    }
    else{
     stack.addAll(stack1);
    }
  }
  public void setStack(Stack<Pair<Map<String, Map<String, Integer>>, Map<String, Integer>>> pStack){
    stack=pStack;
  }
  public void removeStack(){
    stack.removeAllElements();
    stack=null;
  }
  public void print() {
    System.out.println("stack="+stack);

  }


  public List<Formula> getKeyFormulas() {
    return keyFormulas;
  }


  public void setKeyFormulas(List<Formula> pKeyFormulas) {
    keyFormulas=new ArrayList<Formula>();
    keyFormulas.addAll(pKeyFormulas);
  }


  public String getModel() {
    return model;
  }


  public void setModel(String pModel) {
    model = pModel;
  }

}