package com.songstan.ltl_trans.method;

import java.util.ArrayList;
import java.util.List;


public class Transition {

  private String source_state;
  private String target_state;
  private String label;
  private List<Integer> util;
  /**
   *
   */
  public Transition() {
    this.label = "";
    this.source_state = "";
    this.target_state = "";
    this.util=new ArrayList<Integer>();
  }

  public Transition(String labels, String sourceState, String targetState) {
    this.label = labels;
    this.source_state = sourceState;
    this.target_state = targetState;
    this.util=new ArrayList<Integer>();
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public int hashCode() {
    final int PRIME = 1000003;
    int result = 0;
    if (label != null) {
      result = PRIME * result + label.hashCode();
    }
    if (source_state != null) {
      result = PRIME * result + source_state.hashCode();
    }
    if (target_state != null) {
      result = PRIME * result + target_state.hashCode();
    }

    return result;
  }

  public String getSource_state() {
    return source_state;
  }
  public void setSource_state(String pSource_state) {
    source_state = pSource_state;
  }

  public String getTarget_state() {
    return target_state;
  }

  public void setTarget_state(String pTarget_state) {
    target_state = pTarget_state;
  }

  public String getLabel() {
    return label;
  }

  public void setLabel(String plabel) {
    label = plabel;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public boolean equals(Object oth) {
    if (this == oth) { return true; }

    if (oth == null) { return false; }

    if (oth.getClass() != getClass()) { return false; }

    Transition other = (Transition) oth;
    if (this.label == null) {
      if (other.label != null) { return false; }
    } else {
      if (!this.label.equals(other.label)) { return false; }
    }
    if (this.source_state == null) {
      if (other.source_state != null) { return false; }
    } else {
      if (!this.source_state.equals(other.source_state)) { return false; }
    }
    if (this.target_state == null) {
      if (other.target_state != null) { return false; }
    } else {
      if (!this.target_state.equals(other.target_state)) { return false; }
    }
    if(!this.util.equals(other.getUtil())) return false;
    return true;
  }


  public List<Integer> getUtil() {
    return util;
  }


  public void setUtil(List<Integer> pUtil) {
    util = pUtil;
  }
  public boolean addToUtil(int x){
    if(util!=null&&!util.contains(x)){
    util.add(x);
    return true;
    }
    return false;
  }
  /**
   * {@inheritDoc}
   */
  @Override
  public String toString() {
    return source_state + " --" + label + "--> " + target_state;
  }
}
