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
package org.sosy_lab.cpachecker.cpa.automaton;

import java.io.PrintStream;
import java.util.List;
import java.util.Map;

import org.sosy_lab.common.configuration.InvalidConfigurationException;

import com.google.common.collect.Maps;

public class Automaton {
  private final String name;
  /* The internal variables used by the actions/ assignments of this automaton.
   * This reference of the Map is unused because the actions/assignments get their reference from the parser.
   */
  private final Map<String, AutomatonVariable> initVars;
  private final List<AutomatonInternalState> states;
  private final AutomatonInternalState initState;

  public Automaton(String pName, Map<String, AutomatonVariable> pVars, List<AutomatonInternalState> pStates,
      String pInit) throws InvalidAutomatonException {
    this.name = pName;
    this.initVars = pVars;
    this.states = pStates;

    Map<String, AutomatonInternalState> statesMap = Maps.newHashMapWithExpectedSize(pStates.size());
    for (AutomatonInternalState s : pStates) {
      if (statesMap.put(s.getName(), s) != null) {
        throw new InvalidAutomatonException("State " + s.getName() + " exists twice in automaton " + pName);
      }
    }

    initState = statesMap.get(pInit);
    if (initState == null) {
      throw new InvalidAutomatonException("Inital state " + pInit + " not found in automaton " + pName);
    }

    // set the FollowStates of all Transitions
    for (AutomatonInternalState s : pStates) {
      s.setFollowStates(statesMap);
    }
  }

  public List<AutomatonInternalState> getStates() {
    return states;
  }

  public String getName() {
    return name;
  }

  AutomatonInternalState getInitialState() {
    return initState;
  }

  public int getNumberOfStates() {
    return states.size();
  }

  /**
   * Prints the contents of a DOT file representing this automaton to the PrintStream.
   * @param pOut
   */
  void writeDotFile(PrintStream pOut) {
    pOut.println("digraph " + name + "{");

    boolean errorState = false;
    boolean bottomState = false;

    for (AutomatonInternalState s : states) {
      String color = initState.equals(s) ? "green" : "black";

      pOut.println(formatState(s, color));

      for (AutomatonTransition t : s.getTransitions()) {
        pOut.println(formatTransition(s, t));

        errorState = errorState || t.getFollowState().equals(AutomatonInternalState.ERROR);
        bottomState = bottomState || t.getFollowState().equals(AutomatonInternalState.BOTTOM);
      }
    }

    if (errorState) {
      pOut.println(formatState(AutomatonInternalState.ERROR, "red"));
    }

    if (bottomState) {
      pOut.println(formatState(AutomatonInternalState.BOTTOM, "red"));
    }
    pOut.println("}");
  }

  private static String formatState(AutomatonInternalState s, String color) {
    String name = s.getName().replace("_predefinedState_", "");
    return String.format("%d [shape=\"circle\" color=\"%s\" label=\"%s\"]", s.getStateId(), color, name);
  }

  private static String formatTransition(AutomatonInternalState sourceState, AutomatonTransition t) {
    return String.format("%d -> %d [label=\"" /*+ pattern */ + "\"]", sourceState.getStateId(), t.getFollowState().getStateId());
  }


  public Map<String, AutomatonVariable> getInitialVariables() {
    return initVars;
  }

  /**
   * Assert this automaton fulfills the requirements of an ObserverAutomaton.
   * This means the Automaton does not modify other CPAs (Keyword MODIFY) and does not use the BOTTOM element (Keyword STOP).
   * @throws InvalidConfigurationException if the requirements are not fulfilled
   */
  public void assertObserverAutomaton() throws InvalidConfigurationException {
    for (AutomatonInternalState s : this.states) {
        for (AutomatonTransition t : s.getTransitions()) {
          if (!t.meetsObserverRequirements()) {
            throw new InvalidConfigurationException("The transition " + t
                + " in state \"" + s + "\" is not valid for an ObserverAutomaton.");
          }
        }
      }
    }
}
