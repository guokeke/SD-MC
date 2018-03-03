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
package org.sosy_lab.cpachecker.core.algorithm;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.Classes;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.defaults.AbstractSingleWrapperState;
import org.sosy_lab.cpachecker.core.defaults.MergeSepOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.ForcedCovering;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment.Action;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.reachedset.DefaultReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.LocationMappedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.collect.ImmutableSetMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;

@Options(prefix = "cpa")
public class CPAAlgorithm implements Algorithm, StatisticsProvider {

  //public Map<Integer, Pair<AbstractState, Precision>> map = new HashMap<Integer, Pair<AbstractState, Precision>>();//mocode
  public Map<Integer, Pair<AbstractState, Precision>> map1 = new HashMap<Integer, Pair<AbstractState, Precision>>();
  public LinkedHashMap<AbstractState, Precision> maptmp = new LinkedHashMap<AbstractState, Precision>();
  public boolean isExplicit = false;
  public boolean isRefine = false;
  private BufferedWriter wr = null;//mycode
  private StringBuilder sb = new StringBuilder();

  private static class CPAStatistics implements Statistics {

    private Timer totalTimer = new Timer();
    private Timer chooseTimer = new Timer();
    private Timer precisionTimer = new Timer();
    private Timer transferTimer = new Timer();
    private Timer mergeTimer = new Timer();
    private Timer stopTimer = new Timer();
    private Timer addTimer = new Timer();
    private Timer forcedCoveringTimer = new Timer();

    private int countIterations = 0;
    private int maxWaitlistSize = 0;
    private int countWaitlistSize = 0;
    private int countSuccessors = 0;
    private int maxSuccessors = 0;
    private int countMerge = 0;
    private int countStop = 0;
    private int countBreak = 0;


    @Override
    public String getName() {
      return "CPA algorithm";
    }

    @Override
    public void printStatistics(PrintStream out, Result pResult,
        ReachedSet pReached) {
      out.println("Number of iterations:            " + countIterations);
      out.println("Max size of waitlist:            " + maxWaitlistSize);
      out.println("Average size of waitlist:        " + countWaitlistSize
          / (countIterations+1));
      out.println("Number of computed successors:   " + countSuccessors);
      out.println("Max successors for one state:    " + maxSuccessors);
      out.println("Number of times merged:          " + countMerge);
      out.println("Number of times stopped:         " + countStop);
      out.println("Number of times breaked:         " + countBreak);
      out.println();
      out.println("Total time for CPA algorithm:     " + totalTimer + " (Max: " + totalTimer.printMaxTime() + ")");
      out.println("  Time for choose from waitlist:  " + chooseTimer);
      if (forcedCoveringTimer.getNumberOfIntervals() > 0) {
        out.println("  Time for forced covering:       " + forcedCoveringTimer);
      }
      out.println("  Time for precision adjustment:  " + precisionTimer);
      out.println("  Time for transfer relation:     " + transferTimer);
      if (mergeTimer.getNumberOfIntervals() > 0) {
        out.println("  Time for merge operator:        " + mergeTimer);
      }
      out.println("  Time for stop operator:         " + stopTimer);
      out.println("  Time for adding to reached set: " + addTimer);
    }
  }

  @Option(description = "Which strategy to use for forced coverings (empty for none)",
      name = "forcedCovering")
  @ClassOption(packagePrefix = "org.sosy_lab.cpachecker")
  private Class<? extends ForcedCovering> forcedCoveringClass = null;
  private final ForcedCovering forcedCovering;

  private final CPAStatistics stats = new CPAStatistics();

  private final ConfigurableProgramAnalysis cpa;

  private final LogManager logger;

  public CPAAlgorithm(ConfigurableProgramAnalysis cpa, LogManager logger, Configuration config)
      throws InvalidConfigurationException {
    config.inject(this);
    this.cpa = cpa;
    System.out.println("this.cpa=>"+this.cpa.getClass().toString());
    this.logger = logger;

    if (forcedCoveringClass != null) {
      forcedCovering = Classes.createInstance(ForcedCovering.class, forcedCoveringClass,
          new Class<?>[] { Configuration.class, LogManager.class, ConfigurableProgramAnalysis.class },
          new Object[] { config, logger, cpa });
    } else {
      forcedCovering = null;
    }
    sb.append("digraph ARG {\n");
    // default style for nodes
    sb.append("node [style=\"filled\" shape=\"box\" color=\"white\"]\n");
  }

  @Override
  public boolean run(final ReachedSet reachedSet) throws CPAException, InterruptedException {
    stats.totalTimer.start();
    try {
      return run0(reachedSet);
    } finally {
      stats.totalTimer.stop();
      stats.chooseTimer.stop();
      stats.precisionTimer.stop();
      stats.transferTimer.stop();
      stats.mergeTimer.stop();
      stats.stopTimer.stop();
      stats.addTimer.stop();
      stats.forcedCoveringTimer.stop();
    }
  }


  private boolean run0(final ReachedSet reachedSet) throws CPAException, InterruptedException {
    //mycode
    //mycode end
    final TransferRelation transferRelation = cpa.getTransferRelation();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    final StopOperator stopOperator = cpa.getStopOperator();
    final PrecisionAdjustment precisionAdjustment =
        cpa.getPrecisionAdjustment();
    int i = 0;//mycode
    while (reachedSet.hasWaitingState()) {
      i = i + 1;

      CPAchecker.stopIfNecessary();

      stats.countIterations++;

      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration
      int size = reachedSet.getWaitlistSize();
      if (size >= stats.maxWaitlistSize) {
        stats.maxWaitlistSize = size;
      }
      stats.countWaitlistSize += size;

      stats.chooseTimer.start();
      final AbstractState state = reachedSet.popFromWaitlist();
      final Precision precision = reachedSet.getPrecision(state);
      CFANode loc = AbstractStates.extractLocation(state);
      System.out.println(i+","+((ARGState)state).getStateId()+","+loc.getNodeNumber());
      stats.chooseTimer.stop();
      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);
      //System.out.println("state=>"+state);
      //System.out.println(precision);
      if (forcedCovering != null) {
        System.out.println("forcedCovering=>" + forcedCovering.getClass().toString());
        stats.forcedCoveringTimer.start();
        boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);
        stats.forcedCoveringTimer.stop();

        if (stop) {
          // TODO: remove state from reached set?
          continue;
        }
      }
      stats.transferTimer.start();

      Collection<? extends AbstractState> successors =
          transferRelation.getAbstractSuccessors(state, precision, null);//重点
      //Object[] suc = successors.toArray();
     /* if (isExplicit && successors.size() == 2) {
        for (int j = 0; j < 2; j++) {
          AbstractState successor = (AbstractState) suc[j];
          CFAEdge inEdge = AbstractStates.extractLocation(successor).getEnteringEdges().get(0);
          if (inEdge.getDescription().trim().matches("\\[\\!.*")) {
            System.out.println(successors);
          }
          else {
            successors.remove(successor);
          }
        }

      }*/
      stats.transferTimer.stop();
      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.
      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");
      stats.countSuccessors += numSuccessors;
      stats.maxSuccessors = Math.max(numSuccessors, stats.maxSuccessors);

      for (AbstractState successor : Iterables.consumingIterable(successors)) {
        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);
        //System.out.println("precision=>"+precision);
        stats.precisionTimer.start();
        //System.out.println("successor=>"+successor);
        //System.out.println("precisionAdjustment=>"+precisionAdjustment.getClass().toString());
        Triple<AbstractState, Precision, Action> precAdjustmentResult =
            precisionAdjustment.prec(successor, precision, reachedSet);//computing the next state
        stats.precisionTimer.stop();
        successor = precAdjustmentResult.getFirst();
        Precision successorPrecision = precAdjustmentResult.getSecond();
        Action action = precAdjustmentResult.getThird();
       // System.out.println("successor=>"+successor);
        ////System.out.println("successorPrecision=>"+successorPrecision);
        if (action == Action.BREAK) {//find targetable state
          stats.stopTimer.start();
          boolean stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);//重点
          stats.stopTimer.stop();
          if (stop) {
            // don't signal BREAK for covered states
            // no need to call merge and stop either, so just ignore this state
            // and handle next successor
            stats.countStop++;
            logger.log(Level.FINER,
                "Break was signalled but ignored because the state is covered.");
            continue;

          } else {

            stats.countBreak++;
            logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");
            // add the new state
            reachedSet.add(successor, successorPrecision);

            if (!successors.isEmpty()) {
              // re-add the old state to the waitlist, there are unhandled
              // successors left that otherwise would be forgotten
              reachedSet.reAddToWaitlist(state);

            }
            return true;
          }
        }
        assert action == Action.CONTINUE : "Enum Action has unhandled values!";

        Collection<AbstractState> reached = reachedSet.getReached(successor);
        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
        if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
         // System.out.println("进来了");
          stats.mergeTimer.start();
          List<AbstractState> toRemove = new ArrayList<AbstractState>();
          List<Pair<AbstractState, Precision>> toAdd =
              new ArrayList<Pair<AbstractState, Precision>>();

          logger.log(Level.FINER, "Considering", reached.size(),
              "states from reached set for merge");
          for (AbstractState reachedState : reached) {

            AbstractState mergedState =
                mergeOperator.merge(successor, reachedState,
                    successorPrecision);
            if (!mergedState.equals(reachedState)) {
              logger.log(Level.FINER,
                  "Successor was merged with state from reached set");
              logger.log(Level.ALL, "Merged", successor, "\nand",
                  reachedState, "\n-->", mergedState);
              stats.countMerge++;

              toRemove.add(reachedState);
              toAdd.add(Pair.of(mergedState, successorPrecision));
            }
          }
          reachedSet.removeAll(toRemove);
          reachedSet.addAll(toAdd);
          stats.mergeTimer.stop();
        }
        stats.stopTimer.start();
        //System.out.println("stopOperator=>"+stopOperator.getClass().toString());
        //System.out.println("successorPrecision=>"+successorPrecision);
        boolean stop =
            stopOperator.stop(successor, reached, successorPrecision);
        stats.stopTimer.stop();

        if (stop) {
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");
          stats.countStop++;

        } else {
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");
          stats.addTimer.start();
          reachedSet.add(successor, successorPrecision);
          stats.addTimer.stop();
        }
      }
    }
    return true;
  }

  public boolean run(final ReachedSet reachedSet, boolean hasRefine,
      Map<Integer, Pair<AbstractState, Precision>> map,
      Map<Integer, Pair<AbstractState, Precision>> map1) throws CPAException, InterruptedException {
    stats.totalTimer.start();
    try {
      return run0(reachedSet, hasRefine,map,map1);
    } finally {
      stats.totalTimer.stop();
      stats.chooseTimer.stop();
      stats.precisionTimer.stop();
      stats.transferTimer.stop();
      stats.mergeTimer.stop();
      stats.stopTimer.stop();
      stats.addTimer.stop();
      stats.forcedCoveringTimer.stop();
    }
  }

  private boolean run0(final ReachedSet reachedSet, boolean hasRefine,
      Map<Integer, Pair<AbstractState, Precision>> map,
      Map<Integer, Pair<AbstractState, Precision>> map1) throws CPAException, InterruptedException {

    //mycode
    boolean isExplicit = false;
    File file = new File("myARG.dot");
    try {
      wr = new BufferedWriter(new FileWriter(file));
    } catch (IOException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }
    //mycode end
    final TransferRelation transferRelation = cpa.getTransferRelation();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    final StopOperator stopOperator = cpa.getStopOperator();
    final PrecisionAdjustment precisionAdjustment =
        cpa.getPrecisionAdjustment();
    int i = 0;//mycode
    int errorCounter = 0;//mycode
    //Runtime rt=Runtime.getRuntime();
    //System.out.println("CPA算法");
    //mucode
    if (reachedSet.getFirstState().toString().contains("ExplicitState")) {
      isExplicit = true;
    }
    //mycode end
    while (reachedSet.hasWaitingState()) {
      //System.out.println("reachedSet的大小===>"+reachedSet.size());
      i = i + 1;
      CPAchecker.stopIfNecessary();//see:no found
      //System.out.println("我的Map=>"+maptmp);
      stats.countIterations++;

      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration

      int size = reachedSet.getWaitlistSize();
      if (size >= stats.maxWaitlistSize) {
        stats.maxWaitlistSize = size;
      }
      stats.countWaitlistSize += size;

      stats.chooseTimer.start();
      final AbstractState state = reachedSet.popFromWaitlist();
      Precision precision = reachedSet.getPrecision(state);//去掉了final
      /*if (state.getCFANode() != null && map.keySet().contains(state.getCFANode().getLineNumber())) {
        //state.getCFANode().cfaPrecision=precision;
        //precision=map.get(state.getCFANode().getLineNumber()).getSecond();
      }*///mycode

      // System.out.println("precision=>"+precision);
      stats.chooseTimer.stop();
      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);

      if (forcedCovering != null) {
        System.out.println("forcedCovering=>" + forcedCovering.getClass().toString());
        stats.forcedCoveringTimer.start();
        boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);
        stats.forcedCoveringTimer.stop();

        if (stop) {
          // TODO: remove state from reached set?
          continue;
        }
      }
      //System.out.println("parent=>"+((ARGState)state).getParents());
      //System.out.println("state=>" + state);
      //System.out.println("precision=>"+reachedSet.getPrecision(state));
      stats.transferTimer.start();
      //System.out.println("transferrelation="+transferRelation.getClass().toString());
      Collection<? extends AbstractState> successors =
          transferRelation.getAbstractSuccessors(state, precision, null);//重点
      //System.out.println("successors=>" + successors.size());
      Object[] suc = successors.toArray();
   /*   if (isExplicit && successors.size() == 2 && state.getCFANode().getEnteringEdges().size() == 2
          && state.getCFANode().getLeavingEdge().size() == 2) {
        for (int j = 0; j < 2; j++) {
          AbstractState successor = (AbstractState) suc[j];
          //System.out.println("判断后继=>"+successor);
          CFAEdge inEdge = AbstractStates.extractLocation(successor).getEnteringEdges().get(0);
          // System.out.println(inEdge.getDescription().trim());
          if (inEdge.getDescription().trim().matches("\\[\\!.*")) {
            //  System.out.println("go on");
            //System.out.println(successors);
            //continue;
          }
          else {
            //  System.out.println("remove");
            successors.remove(successor);
          }
        }

      }*/

      //System.out.println(successors);
      stats.transferTimer.stop();
      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.
      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");
      stats.countSuccessors += numSuccessors;
      stats.maxSuccessors = Math.max(numSuccessors, stats.maxSuccessors);

      for (AbstractState successor : Iterables.consumingIterable(successors)) {
        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);
        //mycode
        //mycode end
        stats.precisionTimer.start();
        Triple<AbstractState, Precision, Action> precAdjustmentResult =
            precisionAdjustment.prec(successor, precision, reachedSet);//computing the next state
        stats.precisionTimer.stop();
        successor = precAdjustmentResult.getFirst();
        if (successor instanceof AbstractSingleWrapperState) {
          //((AbstractSingleWrapperState) successor).setCFANode();
        }
        Precision successorPrecision = precAdjustmentResult.getSecond();
        //System.out.println("1:=>"+successorPrecision.getClass().toString());
        Action action = precAdjustmentResult.getThird();
        if (action == Action.BREAK) {//find targetable state
          stats.stopTimer.start();
          boolean stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);//重点
          stats.stopTimer.stop();
          if (stop) {
            // don't signal BREAK for covered states
            // no need to call merge and stop either, so just ignore this state
            // and handle next successor
            stats.countStop++;
            logger.log(Level.FINER,
                "Break was signalled but ignored because the state is covered.");
            continue;

          } else {
            stats.countBreak++;
            logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");
            System.out.println("找到ERROR状态");
            // add the new state
            reachedSet.add(successor, successorPrecision);

            if (!successors.isEmpty()) {
              // re-add the old state to the waitlist, there are unhandled
              // successors left that otherwise would be forgotten
              reachedSet.reAddToWaitlist(state);

            }
            //mycode
           /* if (AbstractStates.isTargetState(reachedSet.getLastState())) {
                refinementSuccessful = refine(reachedSet);//start refine->refine call
            }
            if(refinementSuccessful){
              continue;
            }*/
            //printARG(reachedSet);
            //mycode end
            //mycode:to continue to run after finding an error
            /*      int findparent=1;
                  Collection<? extends AbstractState> tmpsuccessors=null;
                  AbstractState tmp=null;
                  AbstractState myNode = successor;
                  AbstractState myNodeGrandpa=null;
                  AbstractState newState=null;
                  while(myNode!=null&&myNode.getCFANode().getLeavingSummaryEdge()==null){
                    Set<ARGState> parent= ((ARGState)myNode).getParents();
                    myNode=parent.iterator().hasNext()?parent.iterator().next():null;
                    findparent++;
                  }
                  //System.out.println("myNode=>"+myNode);
                  if(myNode!=null){
                    Precision myprecision=reachedSet.getPrecision(myNode);
                    findparent=1;
                    myNodeGrandpa=myNode;
                    CFAEdge paEdge=null;
                    while(findparent<3&&myNodeGrandpa!=null){
                      Set<ARGState> parent= ((ARGState)myNodeGrandpa).getParents();
                      myNodeGrandpa  = parent.iterator().hasNext()?parent.iterator().next():null;
                      findparent++;
                      if(findparent==2){
                        paEdge=myNodeGrandpa.getCFANode().getEnteringEdges().get(0);
                      }
                    }
                    if(myNodeGrandpa==null){
                      continue;
                    }
                   // System.out.println("myNodeGrandpa=>"+myNodeGrandpa);
                    CFAEdge edge=myNode.getCFANode().getLeavingSummaryEdge();
                    CFAEdge tmpEdge=new BlankEdge("myedge",myNode.getCFANode().getLineNumber(),edge.getPredecessor(),edge.getSuccessor(),String.valueOf(myNode.getCFANode().getLineNumber()));
                    edge=edge.getSuccessor().getLeavingEdge(0);
                    tmpsuccessors=transferRelation.getAbstractSuccessors(myNode, myprecision,tmpEdge);
                    tmp=tmpsuccessors.iterator().next();
                    stats.precisionTimer.start();
                    Triple<AbstractState, Precision, Action> precAdjustmentResult1 =
                        precisionAdjustment.prec(tmp, myprecision, reachedSet);//computing the next state
                    tmp = precAdjustmentResult1.getFirst();
                    Precision tmpPrecision = precAdjustmentResult1.getSecond();
                    stats.precisionTimer.stop();

                    ((ARGState)myNode).getChildren().remove(tmp);
                    ((ARGState)tmp).getParents().remove(myNode);
                    tmpsuccessors.clear();
                   // System.out.println("tmpState=>"+tmp);
                    if(tmp instanceof AbstractSingleWrapperState){
                      ((AbstractSingleWrapperState)tmp).setCFANode();
                    }
                  //  System.out.println(tmp.getCFANode());
                    tmpsuccessors=transferRelation.getAbstractSuccessors(tmp, tmpPrecision,null);
                    newState=tmpsuccessors.iterator().next();
                    precAdjustmentResult1 =
                        precisionAdjustment.prec(newState, tmpPrecision, reachedSet);
                    newState = precAdjustmentResult1.getFirst();
                    tmpPrecision = precAdjustmentResult1.getSecond();
                    ((ARGState)tmp).getChildren().remove(newState);
                    ((ARGState)newState).getParents().remove(tmp);
                    //System.out.println("newState=>"+newState);
                   // System.out.println(newState!=null);
                    if(newState instanceof AbstractSingleWrapperState){
                        ((AbstractSingleWrapperState)newState).setCFANode();
                    }
                    ((ARGState)myNodeGrandpa).getChildren().clear();
                    ((ARGState)myNodeGrandpa).getChildren().add((ARGState) newState);
                    ((ARGState)newState).getParents().add((ARGState)myNodeGrandpa);
                    if(paEdge!=null){
                      paEdge.setSuccessor(newState.getCFANode());
                    }
                    map.put(newState.getCFANode().getNodeNumber(), newState);
                    reachedSet.add(newState, tmpPrecision);
                    continue;
                  }*/
            //((DefaultReachedSet) reachedSet).safe = false;
            try {
              wr.write(sb.toString() + "\n");
              wr.write("}\n");
              wr.close();
            } catch (IOException e) {
              // TODO Auto-generated catch block
              e.printStackTrace();
            }
            System.out.println("errorCounter=" + errorCounter);
            return true;
          }
        }
        if (refinementSuccessful) {
          continue;
        }
        //System.out.println(action);
        assert action == Action.CONTINUE : "Enum Action has unhandled values!";

        Collection<AbstractState> reached = reachedSet.getReached(successor);

        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
        if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
          stats.mergeTimer.start();
          List<AbstractState> toRemove = new ArrayList<AbstractState>();
          List<Pair<AbstractState, Precision>> toAdd =
              new ArrayList<Pair<AbstractState, Precision>>();

          logger.log(Level.FINER, "Considering", reached.size(),
              "states from reached set for merge");
          for (AbstractState reachedState : reached) {
            AbstractState mergedState =
                mergeOperator.merge(successor, reachedState,
                    successorPrecision);
            if (!mergedState.equals(reachedState)) {
              logger.log(Level.FINER,
                  "Successor was merged with state from reached set");
              logger.log(Level.ALL, "Merged", successor, "\nand",
                  reachedState, "\n-->", mergedState);
              stats.countMerge++;

              toRemove.add(reachedState);
              toAdd.add(Pair.of(mergedState, successorPrecision));
            }
          }
          reachedSet.removeAll(toRemove);
          reachedSet.addAll(toAdd);
          stats.mergeTimer.stop();
        }
        // System.out.println("ok");
        stats.stopTimer.start();
        boolean stop =
            stopOperator.stop(successor, reached, successorPrecision);
        stats.stopTimer.stop();
        if (stop) {
          //System.out.println("stop");
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");
          stats.countStop++;

        } else {
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");
          //int sucNum=successor.getCFANode().getNodeNumber();
          //System.out.println("successorPrecision=>"+successorPrecision.getClass().toString());
          //mycode
         /* if (successor.getCFANode() != null &&
              !successor.getCFANode().getFunctionName().contains("ERROR")
              && map1.containsKey(sucNum)
              && reachedSet.contains(map1.get(successor.getCFANode().getNodeNumber()).getFirst())) {
            AbstractState abs = map1.get(successor.getCFANode().getNodeNumber()).getFirst();
            Precision absPrecision = map1.get(successor.getCFANode().getNodeNumber()).getSecond();
            boolean exist = false;
            Set<ARGState> newParent = new HashSet<ARGState>();
            if (((ARGState) abs).getParents().size() != 0) {
              Iterator<ARGState> parent = ((ARGState) abs).getParents().iterator();
              while (parent.hasNext()) {
                ARGState ps = parent.next();
                if (reachedSet.contains(ps)) {
                  exist = true;
                  newParent.add(ps);
                }
                ps.getChildren().remove(abs);
                ps.getChildren().add((ARGState) successor);
              }
            }
            if (exist) {
              ((ARGState) successor).getParents().clear();
              ((ARGState) successor).getParents().addAll(newParent);
            }
            ((ARGState) abs).getParents().clear();
            if (((ARGState) abs).getChildren().size() != 0) {
              Iterator<ARGState> children = ((ARGState) abs).getChildren().iterator();
              while (children.hasNext()) {
                ARGState cs = children.next();
                cs.getParents().remove(abs);
              }
            }
            ((ARGState) abs).getChildren().clear();
            Precision oldPrecision=reachedSet.getPrecision(abs);
            System.out.println("前OPrecision=>"+oldPrecision);
            System.out.println("前Precision=>"+successorPrecision);
            updatePrecision(successorPrecision,oldPrecision);
            System.out.println("后Precision=>"+successorPrecision);
            //((DefaultReachedSet) reachedSet).remove(abs);
            reachedSet.add(successor, successorPrecision);
            map1.put(sucNum,Pair.of(successor,successorPrecision));
          }
          else {*/
            //mycode  end
            stats.addTimer.start();
            reachedSet.add(successor, successorPrecision);
           // maptmp.put(successor, successorPrecision);
            stats.addTimer.stop();
          //  map1.put(sucNum,Pair.of(successor,successorPrecision));
         //}
        }
      }
    }
    map.clear();
    System.out.println("i=" + i);
    System.out.println("errorCounter=" + errorCounter);
    printARG(reachedSet);
    try {
      wr.write(sb.toString() + "\n");
      wr.write("}\n");
      wr.close();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return true;

  }

  private PredicatePrecision updatePrecision(Precision successorPrecision, Precision pOldPrecision) {
    // TODO Auto-generated method stub
         PredicatePrecision oldPredicatePrecision=Precisions.extractPrecisionByType(pOldPrecision,PredicatePrecision.class);
         PredicatePrecision successorPredicatePrecision=Precisions.extractPrecisionByType(successorPrecision,PredicatePrecision.class);
         Multimap<CFANode,AbstractionPredicate> sucPreds=successorPredicatePrecision.getPredicateMap();
         Multimap<CFANode,AbstractionPredicate> oldPreds=oldPredicatePrecision.getPredicateMap();
         ImmutableSetMultimap.Builder<CFANode, AbstractionPredicate> pmapBuilder = ImmutableSetMultimap.builder();
         pmapBuilder.putAll(oldPreds);
         Iterator<CFANode> oldIterator=oldPreds.keySet().iterator();
         while(oldIterator.hasNext()){
           CFANode loc=oldIterator.next();
           if (!sucPreds.get(loc).containsAll(oldPreds.get(loc))) {
             // new predicates for this location
             pmapBuilder.putAll(loc,oldPreds.get(loc));
             sucPreds.putAll(loc, oldPreds.get(loc));
           }
         }
         ImmutableSetMultimap<CFANode, AbstractionPredicate> newPredicateMap = pmapBuilder.build();
         PredicatePrecision newPrecision;
         newPrecision = new PredicatePrecision(newPredicateMap.values());
    return newPrecision;
  }

  private ReachedSet createInstance(ReachedSet reachedSet) {
    ReachedSet r = null;
    if (reachedSet instanceof LocationMappedReachedSet) {
      r = new LocationMappedReachedSet(((LocationMappedReachedSet) reachedSet).getWaitlistFactory());
    }
    else if (reachedSet instanceof PartitionedReachedSet) {
      r = new PartitionedReachedSet(((PartitionedReachedSet) reachedSet).getWaitlistFactory());
    }
    else {
      r = new DefaultReachedSet(((DefaultReachedSet) reachedSet).getWaitlistFactory());
    }
    return r;
  }

  private void printARG(ReachedSet reachedSet) {
    // TODO Auto-generated method stub
    Deque<ARGState> worklist = new LinkedList<ARGState>();
    Set<ARGState> processed = new HashSet<ARGState>();
    StringBuilder edges = new StringBuilder();
    ARGState lastState = (ARGState) reachedSet.getLastState();
    if (lastState != null)
      worklist.add(lastState);
    String edgeColor = null;
    if (lastState != null && lastState.isTarget()) {
      edgeColor = "color=\"red\" ";
    }
    else {
      edgeColor = "";
    }
    while (worklist.size() != 0) {
      ARGState currentElement = worklist.removeLast();
      if (processed.contains(currentElement)) {
        continue;
      }
      processed.add(currentElement);
      //System.out.println(currentElement);
      String label = ARGUtils.determineLabel(currentElement);
      sb.append(currentElement.getStateId());
      sb.append(" [");
      String color = ARGUtils.determineColor(currentElement);
      ;
      if (color != null) {
        sb.append("fillcolor=\"" + color + "\" ");
      }
      sb.append("label=\"" + label + "\" ");
      sb.append("id=\"" + currentElement.getStateId() + "\"");
      sb.append("]");
      sb.append("\n");

      for (ARGState covered : currentElement.getCoveredByThis()) {
        edges.append(covered.getStateId());
        edges.append(" -> ");
        edges.append(currentElement.getStateId());
        edges.append(" [style=\"dashed\" label=\"covered by\"]\n");
      }

      for (ARGState parent : currentElement.getParents()) {
        StringBuilder edgeTmp = new StringBuilder();
        edgeTmp.append(parent.getStateId());
        edgeTmp.append(" -> ");
        edgeTmp.append(currentElement.getStateId());
        if (!sb.toString().contains(edgeTmp.toString())) {
          edgeTmp.append(" [");
          CFAEdge edge = parent.getEdgeToChild(currentElement);
          edgeTmp.append(edgeColor);
          if (edge != null) {
            // edgeTmp.append(" ");
            edgeTmp.append("label=\"");
            edgeTmp.append("Line ");
            edgeTmp.append(edge.getLineNumber());
            edgeTmp.append(": ");
            edgeTmp.append(edge.getDescription().replaceAll("\n", " ").replace('"', '\''));
            edgeTmp.append("\"");
            edgeTmp.append(" id=\"");
            edgeTmp.append(parent.getStateId());
            edgeTmp.append(" -> ");
            edgeTmp.append(currentElement.getStateId());
            edgeTmp.append("\"");
          }
          edgeTmp.append("]\n");
          edges.append(edgeTmp.toString());
        }
        //System.out.println("包含边"+edgeTmp.toString());
        if (!worklist.contains(parent)) {
          worklist.add(parent);
        }
      }
    }
    sb.append(edges.toString() + "\n");
  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    if (forcedCovering instanceof StatisticsProvider) {
      ((StatisticsProvider) forcedCovering).collectStatistics(pStatsCollection);
    }
    pStatsCollection.add(stats);
  }

  private boolean refine(ReachedSet reached) throws CPAException, InterruptedException {//refine call
    logger.log(Level.FINE, "Error found, performing CEGAR");
    //stats.countRefinements++;
    //sizeOfReachedSetBeforeRefinement = reached.size();
    System.out.println("***********refine*************");
    // System.out.println("2:"+reached.getWaitlist());
    // System.out.println("3:"+reached.getPrecisions());
    // stats.refinementTimer.start();
    boolean refinementResult;
    try {
      refinementResult = mRefiner.performRefinement(reached);//analysis

    } catch (RefinementFailedException e) {
      //   stats.countFailedRefinements++;
      throw e;
    } finally {
      //  stats.refinementTimer.stop();
    }

    logger.log(Level.FINE, "Refinement successful:", refinementResult);

    if (refinementResult) {
      //  stats.countSuccessfulRefinements++;

      //  if (restartOnRefinement) {
      // TODO
      //   }

      runGC();
    }

    return refinementResult;
  }

  private void runGC() {
    if ((++gcCounter % GC_PERIOD) == 0) {
      //stats.gcTimer.start();
      System.gc();
      gcCounter = 0;
      //stats.gcTimer.stop();
    }
  }

  public boolean refinementSuccessful = false;
  public Refiner mRefiner;
  private static final int GC_PERIOD = 100;
  private int gcCounter = 0;
  public static ReachedSet mySet;
  public static int counter = 0;

  @Override
  public Pair<ARGState, ARGState> run(ReachedSet pReached, Proposition pProposition,Set<CFANode> loopHeadNode,CFA cfa) {
    // TODO Auto-generated method stub
    return null;
  }
}
