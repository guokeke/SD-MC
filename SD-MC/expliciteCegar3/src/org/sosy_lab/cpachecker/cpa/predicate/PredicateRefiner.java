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
package org.sosy_lab.cpachecker.cpa.predicate;

import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.cpachecker.util.AbstractStates.*;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interpolation.AbstractInterpolationBasedRefiner;
import org.sosy_lab.cpachecker.util.predicates.interpolation.CounterexampleTraceInfo;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableSetMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

/**
 * This class provides the refinement strategy for the classical predicate
 * abstraction (adding the predicates from the interpolant to the precision
 * and removing the relevant parts of the ARG).
 */
@Options(prefix="cpa.predicate.refinement")
public class PredicateRefiner extends AbstractInterpolationBasedRefiner<Collection<AbstractionPredicate>, Pair<ARGState, CFANode>> implements StatisticsProvider {

  @Option(description="refinement will add all discovered predicates "
          + "to all the locations in the abstract trace")
  private boolean addPredicatesGlobally = false;
  private boolean bool=false;
  private class Stats implements Statistics {
    @Override
    public String getName() {
      return "Predicate Abstraction Refiner";
    }

    @Override
    public void printStatistics(PrintStream out, Result pResult, ReachedSet pReached) {
      PredicateRefiner.this.printStatistics(out, pResult, pReached);
      out.println("  Precision update:               " + precisionUpdate);
      out.println("  ARG update:                     " + argUpdate);
    }
  }

  private final Timer precisionUpdate = new Timer();
  private final Timer argUpdate = new Timer();

  public static PredicateRefiner create(ConfigurableProgramAnalysis pCpa) throws CPAException, InvalidConfigurationException {
    PredicateCPA predicateCpa = CPAs.retrieveCPA(pCpa, PredicateCPA.class);
    if (predicateCpa == null) {
      throw new InvalidConfigurationException(PredicateRefiner.class.getSimpleName() + " needs a PredicateCPA");
    }

    LogManager logger = predicateCpa.getLogger();

    PredicateRefinementManager manager = new PredicateRefinementManager(predicateCpa.getFormulaManager(),
                                          predicateCpa.getPathFormulaManager(),
                                          predicateCpa.getSolver(),
                                          predicateCpa.getAbstractionManager(),
                                          predicateCpa.getFormulaManagerFactory(),
                                          predicateCpa.getConfiguration(),
                                          logger);

    return new PredicateRefiner(predicateCpa.getConfiguration(), logger, pCpa, manager);
  }

  public PredicateRefiner(final Configuration config, final LogManager logger,
      final ConfigurableProgramAnalysis pCpa,
      final PredicateRefinementManager pInterpolationManager) throws CPAException, InvalidConfigurationException {

    super(config, logger, pCpa, pInterpolationManager);

    config.inject(this, PredicateRefiner.class);
  }
  @Override
  protected final List<Pair<ARGState, CFANode>> transformPath(Path pPath) {
    List<Pair<ARGState, CFANode>> result = Lists.newArrayList();

    for (ARGState ae : from(pPath).skip(1).transform(Pair.<ARGState>getProjectionToFirst())) {
      PredicateAbstractState pe = extractStateByType(ae, PredicateAbstractState.class);
      if (pe.isAbstractionState()) {
        CFANode loc = AbstractStates.extractLocation(ae);
        result.add(Pair.of(ae, loc));
      }
    }

    assert pPath.getLast().getFirst() == result.get(result.size()-1).getFirst();
    return result;
  }

  private static final Function<PredicateAbstractState, Formula> GET_BLOCK_FORMULA
                = new Function<PredicateAbstractState, Formula>() {
                    @Override
                    public Formula apply(PredicateAbstractState e) {
                      assert e.isAbstractionState();
                      ////System.out.println("e=>"+e.getClass().toString());
                      return e.getAbstractionFormula().getBlockFormula();
                    }
                  };

  @Override
  protected List<Formula> getFormulasForPath(List<Pair<ARGState, CFANode>> path, ARGState initialState) throws CPATransferException {
    return from(path)
        .transform(Pair.<ARGState>getProjectionToFirst())
        .transform(toState(PredicateAbstractState.class))
        .transform(GET_BLOCK_FORMULA)
        .toImmutableList();
  }

  @Override
  protected void performRefinement(ARGReachedSet pReached,
      List<Pair<ARGState, CFANode>> pPath,
      CounterexampleTraceInfo<Collection<AbstractionPredicate>> pCounterexample,
      boolean pRepeatedCounterexample) throws CPAException {
    precisionUpdate.start();
    // get previous precision
    UnmodifiableReachedSet reached = pReached.asReachedSet();
    Precision oldPrecision = reached.getPrecision(reached.getLastState());
    ////System.out.println("我的:"+oldPrecision.getClass().toString());
    PredicatePrecision oldPredicatePrecision = Precisions.extractPrecisionByType(oldPrecision, PredicatePrecision.class);
    ////System.out.println("         oldPrecision=>"+oldPrecision);
    //System.out.println("oldPredicatePrecision=>"+oldPredicatePrecision);
    ////System.out.println("      pCounterexample=>"+pCounterexample);
    if (oldPredicatePrecision == null) {
      throw new IllegalStateException("Could not find the PredicatePrecision for the error element");
    }

    Pair<ARGState, PredicatePrecision> refinementResult =
            performRefinement(oldPredicatePrecision, pPath, pCounterexample, pRepeatedCounterexample);
    precisionUpdate.stop();

    argUpdate.start();
    if(refinementResult!=null&&refinementResult.getSecond()==null){
      pReached.removeSubtree1(refinementResult.getFirst());
     // refinementResult.getFirst().removeFromARG();
    }
    else if(refinementResult!=null){
      //bool=false;
      pReached.removeSubtree(refinementResult.getFirst(), refinementResult.getSecond());
    }
    else{
     ARGState last= (ARGState) pReached.asReachedSet().getLastState();
     if(last!=null){
       last.removeFromARG();
       pReached.asReachedSet().remove(last);
     }
    }
    argUpdate.stop();
  }


  private Pair<ARGState, PredicatePrecision> performRefinement(PredicatePrecision oldPrecision,
      List<Pair<ARGState, CFANode>> pPath,
      CounterexampleTraceInfo<Collection<AbstractionPredicate>> pInfo,
      boolean pRepeatedCounterexample) throws CPAException {
    List<Collection<AbstractionPredicate>> newPreds = pInfo.getPredicatesForRefinement();
    //System.out.println("newPreds=>"+newPreds);
    List<Pair<ARGState, CFANode>> interpolationPoints = pPath.subList(0, pPath.size()-1);//去掉pPath中errorstate对应的项
    assert interpolationPoints.size() == newPreds.size();
    Multimap<CFANode, AbstractionPredicate> oldPredicateMap = oldPrecision.getPredicateMap();
    Set<AbstractionPredicate> globalPredicates = oldPrecision.getGlobalPredicates();
    //
    /*  Iterator<CFANode> cn=oldPredicateMap.keySet().iterator();
      while(cn.hasNext()){
        CFANode node=cn.next();
        //System.out.println(node.toString()+":"+oldPredicateMap.get(node));
      }
      */
    //
    boolean predicatesFound = false;
    boolean newPredicatesFound = false;
    Pair<ARGState, CFANode> firstInterpolationPoint = null;
    ImmutableSetMultimap.Builder<CFANode, AbstractionPredicate> pmapBuilder = ImmutableSetMultimap.builder();

    pmapBuilder.putAll(oldPredicateMap);

    // iterate through interpolationPoints and find first point with new predicates, from there we have to cut the ARG
    // also build new precision
    int i = 0;
    ARGState first=null;
    for (Pair<ARGState, CFANode> interpolationPoint : interpolationPoints) {
      Collection<AbstractionPredicate> localPreds = newPreds.get(i++);
      if (localPreds.size() > 0) {
        // found predicates
        predicatesFound = true;
        CFANode loc = interpolationPoint.getSecond();

        if (firstInterpolationPoint == null) {
          firstInterpolationPoint = interpolationPoint;
        }
        if (!oldPredicateMap.get(loc).containsAll(localPreds)) {
          // new predicates for this location
          newPredicatesFound = true;
          pmapBuilder.putAll(loc, localPreds);
          pmapBuilder.putAll(loc, globalPredicates);
        }
        else if(first==null&&localPreds.size()==1){
          AbstractionPredicate ap=localPreds.iterator().next();
          if(ap.getSymbolicAtom().isFalse())
            first=interpolationPoint.getFirst();
        }
      }
    }
    if (!predicatesFound) {
      // The only reason why this might appear is that the very last block is
      // infeasible in itself, however, we check for such cases during strengthen,
      // so they shouldn't appear here.
      throw new RefinementFailedException(RefinementFailedException.Reason.InterpolationFailed, null);
    }
    assert firstInterpolationPoint != null;
    ImmutableSetMultimap<CFANode, AbstractionPredicate> newPredicateMap = pmapBuilder.build();
    //System.out.println("***************我的Predicate***************");
  //
    //System.out.println("*******newPredicatePrecision*********");
//    Iterator<CFANode> cn1=newPredicateMap.keySet().iterator();
//    while(cn1.hasNext()){
//      CFANode node=cn1.next();
//      //System.out.println(node.toString()+":"+newPredicateMap.get(node));
//    }
  //
    PredicatePrecision newPrecision;
    if (addPredicatesGlobally) {
     // MyInfo.newPrecision=new PredicatePrecision(newPredicateMap.values());
      newPrecision = new PredicatePrecision(newPredicateMap.values());
    } else {
    //  MyInfo.newPrecision=new PredicatePrecision(newPredicateMap, globalPredicates);
      newPrecision = new PredicatePrecision(newPredicateMap, globalPredicates);
    }
    //System.out.println("newPrecision=>"+newPrecision);
    logger.log(Level.ALL, "Predicate map now is", newPredicateMap);

    // We have two different strategies for the refinement root: set it to
    // the firstInterpolationPoint or set it to highest location in the ARG
    // where the same CFANode appears.
    // Both work, so this is a heuristics question to get the best performance.
    // My benchmark showed, that at least for the benchmarks-lbe examples it is
    // best to use strategy one iff newPredicatesFound.

    ARGState root = null;
   // //System.out.println("newPredication=>"+newPredicatesFound);
    if (newPredicatesFound) {
      root = firstInterpolationPoint.getFirst();

      logger.log(Level.FINEST, "Found spurious counterexample,",
          "trying strategy 1: remove everything below", root, "from ARG.");

    } else {

//      if(first!=null){
//        first.removeFromARG();
//      }
//      if (pRepeatedCounterexample) {
//        throw new RefinementFailedException(RefinementFailedException.Reason.RepeatedCounterexample, null);
//      }



//      ////System.out.println("here");
//      CFANode loc = firstInterpolationPoint.getSecond();
//
//      logger.log(Level.FINEST, "Found spurious counterexample,",
//          "trying strategy 2: remove everything below node", loc, "from ARG.");

      // find first element in path with location == loc,
      // this is not necessary equal to firstInterpolationPoint.getFirst()
      for (Pair<ARGState, CFANode> abstractionPoint : pPath) {
        ARGState first1=abstractionPoint.getFirst();
        PredicateAbstractState abstraction = AbstractStates.extractStateByType(first1, PredicateAbstractState.class);
        if(abstraction != null && abstraction.isAbstractionState()){
           Formula f=abstraction.getAbstractionFormula().asFormula();
           if(f.toString().equals("(ite false false true)")){
             bool=true;
             return Pair.of(first1,null);

             //break;
           }
        }
//        if (abstractionPoint.getSecond().equals(loc)) {
//          root = abstractionPoint.getFirst();
//          break;
//        }
      }
      return null;
//      if (root == null) {
//        throw new CPAException("Inconsistent ARG, did not find element for " + loc);
//      }interpolationPoints.get(2).getFirst()
    }
    return Pair.of(interpolationPoints.get(2).getFirst(), newPrecision);
  }
  private Pair<AbstractState, Precision> performRefinement1(PredicatePrecision oldPrecision,
      List<Pair<ARGState, CFANode>> pPath,
      CounterexampleTraceInfo<Collection<AbstractionPredicate>> pInfo,
      boolean pRepeatedCounterexample) throws CPAException {
    List<Collection<AbstractionPredicate>> newPreds = pInfo.getPredicatesForRefinement();
    //System.out.println("newPreds=>"+newPreds.size());
    if(newPreds.size()==0)
      return null;
    List<Pair<ARGState, CFANode>> interpolationPoints =new ArrayList<Pair<ARGState, CFANode>>();//去掉pPath中errorstate对应的项
    interpolationPoints.add(pPath.get(pPath.size()-3));
    interpolationPoints.add(pPath.get(pPath.size()-2));
    interpolationPoints.add(pPath.get(pPath.size()-1));

    assert interpolationPoints.size() == newPreds.size();
    Multimap<CFANode, AbstractionPredicate> oldPredicateMap = oldPrecision.getPredicateMap();
    Set<AbstractionPredicate> globalPredicates = oldPrecision.getGlobalPredicates();
    boolean predicatesFound = false;
    boolean newPredicatesFound = false;
    Pair<ARGState, CFANode> firstInterpolationPoint = null;
    ImmutableSetMultimap.Builder<CFANode, AbstractionPredicate> pmapBuilder = ImmutableSetMultimap.builder();

    pmapBuilder.putAll(oldPredicateMap);

    // iterate through interpolationPoints and find first point with new predicates, from there we have to cut the ARG
    // also build new precision
    int i = 0;
    for (Pair<ARGState, CFANode> interpolationPoint : interpolationPoints) {
      Collection<AbstractionPredicate> localPreds = newPreds.get(i++);
      if (localPreds.size() > 0) {
        // found predicates
        predicatesFound = true;
        CFANode loc = interpolationPoint.getSecond();

        if (firstInterpolationPoint == null) {
          firstInterpolationPoint = interpolationPoint;
        }
        if (!oldPredicateMap.get(loc).containsAll(localPreds)) {
          // new predicates for this location
          newPredicatesFound = true;
          pmapBuilder.putAll(loc, localPreds);
          pmapBuilder.putAll(loc, globalPredicates);
        }
      }
    }
    if (!predicatesFound) {
      return null;
    }
    //assert firstInterpolationPoint != null;
    ImmutableSetMultimap<CFANode, AbstractionPredicate> newPredicateMap = pmapBuilder.build();
    //System.out.println("***************我的Predicate***************");
  //
    //System.out.println("*******newPredicatePrecision*********");
    Iterator<CFANode> cn1=newPredicateMap.keySet().iterator();
    while(cn1.hasNext()){
      CFANode node=cn1.next();
      //System.out.println(node.toString()+":"+newPredicateMap.get(node));
    }
  //
    PredicatePrecision newPrecision;
    if (addPredicatesGlobally) {
      newPrecision = new PredicatePrecision(newPredicateMap.values());
    } else {
      newPrecision = new PredicatePrecision(newPredicateMap, globalPredicates);
    }
    //System.out.println("newPrecision=>"+newPrecision);
    logger.log(Level.ALL, "Predicate map now is", newPredicateMap);

    // We have two different strategies for the refinement root: set it to
    // the firstInterpolationPoint or set it to highest location in the ARG
    // where the same CFANode appears.
    // Both work, so this is a heuristics question to get the best performance.
    // My benchmark showed, that at least for the benchmarks-lbe examples it is
    // best to use strategy one iff newPredicatesFound.

    ARGState root = null;
   // //System.out.println("newPredication=>"+newPredicatesFound);
    if (newPredicatesFound) {
      root = firstInterpolationPoint.getFirst();

      logger.log(Level.FINEST, "Found spurious counterexample,",
          "trying strategy 1: remove everything below", root, "from ARG.");

    } else {

      //if (pRepeatedCounterexample) {
      //  throw new RefinementFailedException(RefinementFailedException.Reason.RepeatedCounterexample, null);
      //}
      ////System.out.println("here");
      CFANode loc = firstInterpolationPoint.getSecond();

      logger.log(Level.FINEST, "Found spurious counterexample,",
          "trying strategy 2: remove everything below node", loc, "from ARG.");

      // find first element in path with location == loc,
      // this is not necessary equal to firstInterpolationPoint.getFirst()
      for (Pair<ARGState, CFANode> abstractionPoint : pPath) {
        if (abstractionPoint.getSecond().equals(loc)) {
          root = abstractionPoint.getFirst();
          break;
        }
      }
      if (root == null) {
        throw new CPAException("Inconsistent ARG, did not find element for " + loc);
      }
    }
   // root.setDestroyed(true);
    ARGState parent=root.getParents().iterator().next();
    return Pair.of((AbstractState)parent, (Precision)newPrecision);
  }
  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    pStatsCollection.add(new Stats());
  }
}
