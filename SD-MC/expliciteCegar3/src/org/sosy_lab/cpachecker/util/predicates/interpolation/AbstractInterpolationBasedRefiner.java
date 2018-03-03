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
package org.sosy_lab.cpachecker.util.predicates.interpolation;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.AbstractARGBasedRefiner;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.globalinfo.SSAMapInfo;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.collect.Multiset;
import com.songstan.ltl_trans.method.Transition;

/**
 * This class provides a basic refiner implementation for predicate analysis.
 * When a counterexample is found, it creates a path for it and checks it for
 * feasibiltiy, getting the interpolants if possible.
 *
 * It does not define any strategy for using the interpolants to update the
 * abstraction, this is left to sub-classes.
 *
 * It does, however, produce a nice error path in case of a feasible counterexample.
 *
 * @param <I> The type of the result of the interpolation query.
 * @param <P> The type of path elements used by the sub-class.
 */
@Options(prefix="cpa.predicate.refinement")
public abstract class AbstractInterpolationBasedRefiner<I, P> extends AbstractARGBasedRefiner {

  @Option(name="msatCexFile",
      description="where to dump the counterexample formula in case the error location is reached")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private File dumpCexFile = new File("counterexample.msat");

  public final Timer totalRefinement = new Timer();
  public final Timer errorPathProcessing = new Timer();

  protected final LogManager logger;

  private final InterpolationManager<I> formulaManager;

  // TODO: this should be private
  protected List<Formula> lastErrorPath = null;
  protected AbstractInterpolationBasedRefiner(final Configuration config, LogManager pLogger, final ConfigurableProgramAnalysis pCpa, InterpolationManager<I> pInterpolationManager) throws CPAException, InvalidConfigurationException {
    super(pCpa);
    config.inject(this, AbstractInterpolationBasedRefiner.class);
    logger = pLogger;
    formulaManager = pInterpolationManager;
  }
  @Override
  protected CounterexampleInfo performRefinementForProperty(final AbstractState successor, final CFANode loc,Proposition pProposition,String checkType,boolean b) throws CPAException, InterruptedException {
    totalRefinement.start();
    ///Set<ARGState> elementsOnPath = ARGUtils.getAllStatesOnPathsTo(pPath.getLast().getFirst()); // TODO: make this lazy?
    //System.out.println("elementsOnPath=>"+elementsOnPath);
   // boolean branchingOccurred = true;
    //if (elementsOnPath.size() == pPath.size()) {
      // No branches/merges in path, it is precise.
      // We don't need to care about creating extra predicates for branching etc.
    //  elementsOnPath = Collections.emptySet();
    //  branchingOccurred = false;
   // }

    logger.log(Level.FINEST, "Starting interpolation-based refinement");

    // create path with all abstraction location elements (excluding the initial element)
    // the last element is the element corresponding to the error location
   // final List<P> path = transformPath(pPath);
    ///logger.log(Level.ALL, "Abstraction trace is", path);
    ///if(path.size()==0)
    ///  return null;
    // create list of formulas on path
    List<Formula> formulas = ((ARGState) successor).getKeyFormulas();//getFormulasForPath(path, pPath.getFirst().getFirst());//把edges转为formulas
    if(formulas==null){
      //formulas=new ArrayList<Formula>();
      List<Formula> formulas1=new ArrayList<Formula>();
      Path pPath=ARGUtils.getOnePathTo(((ARGState) successor).getParents().iterator().next());



      final List<P> path = transformPath(pPath);
      formulas1=getFormulasForPath(path, pPath.getFirst().getFirst());
     // formulas.addAll(formulas);

      /*<yangkai>*/
      List<CFAEdge> edgeList = pPath.asEdgesList();//<yangkai>得到边链表
      List<Formula> formulas2=new ArrayList<Formula>();//关键边链表
      int index=0;
      for(CFAEdge e : edgeList){
        if(e.isKeyEdge()){
          formulas2.add(formulas1.get(index));
        }
        index++;
      }

      ((ARGState)successor).setForlumas(formulas2);
      formulas =((ARGState)successor).getFormulas();
    }
    //assert path.size() == formulas.size();
    //System.out.println("path=>"+path);
    //System.out.println("formulaManager=>"+formulaManager.getClass().toString());
    CounterexampleTraceInfo<I> counterexample=null;
    if(checkType.equals("pointercheck"))
     counterexample = formulaManager.buildCounterexampleTraceForPointer(formulas,successor,loc,pProposition,b);
    else if(checkType.equals("simplepropertycheck")){
      counterexample = formulaManager.buildCounterexampleTraceForSimpleProperty(formulas,successor,loc,pProposition,b);
    }
    else if(checkType.equals("arraycheck")){
      counterexample = formulaManager.buildCounterexampleTraceForArray(formulas,successor,loc,pProposition,b);
    }

    // if error is spurious refine
    if (counterexample!=null&&counterexample.isSpurious()) {
      logger.log(Level.FINEST, "Error trace is spurious, refining the abstraction");
     // boolean repeatedCounterexample = formulas.equals(lastErrorPath);
      //lastErrorPath = formulas;
      //performRefinement1(pReached, path, counterexample, repeatedCounterexample);
      //totalRefinement.stop();
      CounterexampleInfo cexInfo=CounterexampleInfo.spurious();
      cexInfo.setProposition(counterexample.getProposition());
      return cexInfo;
    }
    CounterexampleInfo cexInfo=CounterexampleInfo.unSpurious();
    cexInfo.setProposition(counterexample.getProposition());
    return cexInfo;
  }

  @Override
  protected CounterexampleInfo performRefinement(final ARGReachedSet pReached, final Path pPath) throws CPAException, InterruptedException {
    totalRefinement.start();

    Set<ARGState> elementsOnPath = ARGUtils.getAllStatesOnPathsTo(pPath.getLast().getFirst()); // TODO: make this lazy?
    //System.out.println("elementsOnPath=>"+elementsOnPath);
    boolean branchingOccurred = true;
    if (elementsOnPath.size() == pPath.size()) {
      // No branches/merges in path, it is precise.
      // We don't need to care about creating extra predicates for branching etc.
      elementsOnPath = Collections.emptySet();
      branchingOccurred = false;
    }

    logger.log(Level.FINEST, "Starting interpolation-based refinement");

    // create path with all abstraction location elements (excluding the initial element)
    // the last element is the element corresponding to the error location
    final List<P> path = transformPath(pPath);
    logger.log(Level.ALL, "Abstraction trace is", path);

    // create list of formulas on path
    final List<Formula> formulas = getFormulasForPath(path, pPath.getFirst().getFirst());//把edges转为formulas
    assert path.size() == formulas.size();
    Multiset<String> set=SSAMapInfo.getInstance().getVars();

    //<yangkai> 根据路径公式formulas将对应的输入变量的变量名保存到values中
    List<CFAEdge> edgeList = pPath.asEdgesList();
    List<Formula> formulas2=new ArrayList<Formula>();//关键边链表
    int index=0;
    for(CFAEdge e : edgeList){
      if(e==null){
        continue;
      }
      if(e.isKeyEdge()){
        formulas2.add(formulas.get(index));
      }
      index++;
    }


    final CounterexampleTraceInfo<I> counterexample = formulaManager.buildCounterexampleTrace(formulas2, elementsOnPath);
    // if error is spurious refine
    if (counterexample.isSpurious()) {

      logger.log(Level.FINEST, "Error trace is spurious, refining the abstraction");
      boolean repeatedCounterexample = formulas.equals(lastErrorPath);
      lastErrorPath = formulas;
      performRefinement(pReached, path, counterexample, repeatedCounterexample);
      totalRefinement.stop();
        return CounterexampleInfo.spurious();
    }
    else {//静态找到一个反例时需要调用动态执行判断是否为真反例

      // we have a real error
      //System.out.println("ARGReachedSet的大小=>"+pReached.asReachedSet().size());//还没有删除reached中的状态
      //System.out.println("path=>"+path);
      Iterator<ARGState> allIt=pPath.getStateSet().iterator();
      while(allIt.hasNext()){
        allIt.next().setMyTarget(true);
      }
      logger.log(Level.FINEST, "Error trace is not spurious");
      final Path targetPath;
      final CounterexampleTraceInfo<I> preciseCounterexample;

      if (branchingOccurred) {
        Pair<Path, CounterexampleTraceInfo<I>> preciseInfo = findPreciseErrorPath(pPath, counterexample);

        if (preciseInfo != null) {
          targetPath = preciseInfo.getFirst();
          preciseCounterexample = preciseInfo.getSecond();
        } else {
          logger.log(Level.WARNING, "The error path and the satisfying assignment may be imprecise!");
          targetPath = pPath;
          preciseCounterexample = counterexample;
        }
      } else {
        targetPath = pPath;
        preciseCounterexample = counterexample;
      }
      //System.out.println("我运行到这里了");
      CounterexampleInfo cex = CounterexampleInfo.feasible(targetPath, preciseCounterexample.getCounterexample());
      //System.out.println("ARGReachedSet的大小=>"+pReached.asReachedSet().size());
      cex.addFurtherInformation(new Object() {
        // lazily call formulaManager.dumpCounterexample()
        @Override
        public String toString() {
          return formulaManager.dumpCounterexample(preciseCounterexample);
        }
      }, dumpCexFile);

      totalRefinement.stop();
      return cex;
    }
  }

  protected abstract List<P> transformPath(Path pPath);

  /**
   * Get the block formulas from a path.
   * @param path A list of all abstraction elements
   * @param initialState The initial element of the analysis (= the root element of the ARG)
   * @return A list of block formulas for this path.
   * @throws CPATransferException
   */
  protected abstract List<Formula> getFormulasForPath(List<P> path, ARGState initialState) throws CPATransferException;

  protected abstract void performRefinement(ARGReachedSet pReached, List<P> path,
      CounterexampleTraceInfo<I> counterexample, boolean pRepeatedCounterexample) throws CPAException;
  private Pair<Path, CounterexampleTraceInfo<I>> findPreciseErrorPath(Path pPath, CounterexampleTraceInfo<I> counterexample) {
    errorPathProcessing.start();
    try {

      Map<Integer, Boolean> preds = counterexample.getBranchingPredicates();
      if (preds.isEmpty()) {
        logger.log(Level.WARNING, "No information about ARG branches available!");
        return null;
      }

      // find correct path
      Path targetPath;
      try {
        ARGState root = pPath.getFirst().getFirst();
        ARGState target = pPath.getLast().getFirst();
        Set<ARGState> pathElements = ARGUtils.getAllStatesOnPathsTo(target);

        targetPath = ARGUtils.getPathFromBranchingInformation(root, target,
            pathElements, preds);

      } catch (IllegalArgumentException e) {
        logger.logUserException(Level.WARNING, e, null);
        return null;
      }

      // try to create a better satisfying assignment by replaying this single path
      CounterexampleTraceInfo<I> info2;
      try {
        info2 = formulaManager.checkPath(targetPath.asEdgesList());

      } catch (CPATransferException e) {
        // path is now suddenly a problem
        logger.logUserException(Level.WARNING, e, "Could not replay error path");
        return null;
      }

      if (info2.isSpurious()) {
        logger.log(Level.WARNING, "Inconsistent replayed error path!");
        return null;

      } else {
        return Pair.of(targetPath, info2);
      }

    } finally {
      errorPathProcessing.stop();
    }
  }

  protected void printStatistics(PrintStream out, Result result, ReachedSet reached) {

    if (totalRefinement.getSumTime() > 0) {
      out.println("Time for refinement:              " + totalRefinement);
      formulaManager.stats.printStatistics(out, result, reached);
      out.println("  Error path post-processing:     " + errorPathProcessing);
    }
  }
  @Override
  public void generateOneStepFormula(List<Formula> formulas,PathFormula pathFormula,CFAEdge sucEdge,Transition transition,Proposition proposition){
    formulaManager.generateOneStepFormula(formulas, pathFormula, sucEdge, transition, proposition);
  }

}