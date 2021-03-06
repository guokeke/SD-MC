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
import static com.google.common.collect.Iterables.getOnlyElement;
import static org.sosy_lab.cpachecker.util.AbstractStates.*;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.blocks.BlockPartitioning;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.interfaces.WrapperCPA;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.abm.AbstractABMBasedRefiner;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.cpa.predicate.relevantpredicates.RefineableRelevantPredicatesComputer;
import org.sosy_lab.cpachecker.cpa.predicate.relevantpredicates.RelevantPredicatesComputer;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interpolation.CounterexampleTraceInfo;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.base.Function;
import com.google.common.collect.Lists;


/**
 * Implements predicate refinements when using ABM.
 * It is based on the {@link AbstractABMBasedRefiner} and delegates the work to
 * a {@link ExtendedPredicateRefiner}, which is a small extension of the regular
 * {@link PredicateRefiner}.
 *
 * So the hierarchy is as follows:
 *
 *               AbstractARGBasedRefiner
 *                         ^
 *                         |
 *           +-------------+-------------+
 *           |                           |
 * AbstractABMBasedRefiner   AbstractInterpolationBasedRefiner
 *           ^                           ^
 *           |                           |
 *           |                    PredicateRefiner
 *           |                           ^
 *           |                           |
 *   ABMPredicateRefiner ---> ExtendedPredicateRefiner
 *
 * Here ^ means inheritance and -> means reference.
 */
public final class ABMPredicateRefiner extends AbstractABMBasedRefiner implements StatisticsProvider {

  private final ExtendedPredicateRefiner refiner;


  public static Refiner create(ConfigurableProgramAnalysis pCpa) throws CPAException, InvalidConfigurationException {
    return new ABMPredicateRefiner(pCpa);
  }

  public ABMPredicateRefiner(final ConfigurableProgramAnalysis pCpa) throws CPAException, InvalidConfigurationException {

    super(pCpa);

    if (!(pCpa instanceof WrapperCPA)) {
      throw new InvalidConfigurationException(ABMPredicateRefiner.class.getSimpleName() + " could not find the PredicateCPA");
    }

    ABMPredicateCPA predicateCpa = ((WrapperCPA)pCpa).retrieveWrappedCpa(ABMPredicateCPA.class);
    if (predicateCpa == null) {
      throw new InvalidConfigurationException(ABMPredicateRefiner.class.getSimpleName() + " needs an ABMPredicateCPA");
    }

    LogManager logger = predicateCpa.getLogger();

    PredicateRefinementManager manager = new PredicateRefinementManager(predicateCpa.getFormulaManager(),
                                          predicateCpa.getPathFormulaManager(),
                                          predicateCpa.getSolver(),
                                          predicateCpa.getAbstractionManager(),
                                          predicateCpa.getFormulaManagerFactory(),
                                          predicateCpa.getConfiguration(),
                                          logger);

    this.refiner = new ExtendedPredicateRefiner(predicateCpa.getConfiguration(),
        logger, pCpa, predicateCpa, manager);
  }

  @Override
  protected final CounterexampleInfo performRefinement0(ARGReachedSet pReached, Path pPath)
      throws CPAException, InterruptedException {

    return refiner.performRefinement(pReached, pPath);
  }

  /**
   * This is a small extension of PredicateRefiner that overrides
   * {@link #getFormulasForPath(List, ARGState)} so that it respects ABM.
   */
  static final class ExtendedPredicateRefiner extends PredicateRefiner {

    final Timer ssaRenamingTimer = new Timer();

    private final PathFormulaManager pfmgr;
    private final RefineableRelevantPredicatesComputer relevantPredicatesComputer;
    private final ABMPredicateCPA predicateCpa;

    private List<Region> lastAbstractions = null;
    private boolean refinedLastRelevantPredicatesComputer = false;

    private ExtendedPredicateRefiner(final Configuration config, final LogManager logger,
        final ConfigurableProgramAnalysis pCpa,
        final ABMPredicateCPA predicateCpa,
        final PredicateRefinementManager pInterpolationManager) throws CPAException, InvalidConfigurationException {

      super(config, logger, pCpa, pInterpolationManager);

      pfmgr = predicateCpa.getPathFormulaManager();

      RelevantPredicatesComputer relevantPredicatesComputer = predicateCpa.getRelevantPredicatesComputer();
      if (relevantPredicatesComputer instanceof RefineableRelevantPredicatesComputer) {
        this.relevantPredicatesComputer = (RefineableRelevantPredicatesComputer)relevantPredicatesComputer;
      } else {
        this.relevantPredicatesComputer = null;
      }

      this.predicateCpa = predicateCpa;

      predicateCpa.getABMStats().addRefiner(this);
    }

    /**
     * Overridden just for visibility
     */
    @Override
    protected final CounterexampleInfo performRefinement(ARGReachedSet pReached, Path pPath) throws CPAException, InterruptedException {
      return super.performRefinement(pReached, pPath);
    }

    private static final Function<PredicateAbstractState, Region> GET_REGION
    = new Function<PredicateAbstractState, Region>() {
        @Override
        public Region apply(PredicateAbstractState e) {
          assert e.isAbstractionState();
          return e.getAbstractionFormula().asRegion();
        }
      };

    private List<Region> getRegionsForPath(List<Pair<ARGState, CFANode>> path) throws CPATransferException {
      return from(path)
              .transform(Pair.<ARGState>getProjectionToFirst())
              .transform(toState(PredicateAbstractState.class))
              .transform(GET_REGION)
              .toImmutableList();
    }

    @Override
    protected void performRefinement(
        ARGReachedSet pReached,
        List<Pair<ARGState, CFANode>> pPath,
        CounterexampleTraceInfo<Collection<AbstractionPredicate>> pCounterexample,
        boolean pRepeatedCounterexample) throws CPAException {

      // overriding this method is needed, as, in principle, it is possible to get two successive spurious counterexamples
      // which only differ in its abstractions (with 'aggressive caching').

      boolean refinedRelevantPredicatesComputer = false;

      if (pRepeatedCounterexample) {
        //block formulas are the same as last time; check if abstractions also agree
        pRepeatedCounterexample = getRegionsForPath(pPath).equals(lastAbstractions);

        if (pRepeatedCounterexample && !refinedLastRelevantPredicatesComputer && relevantPredicatesComputer != null) {
          //even abstractions agree; try refining relevant predicates reducer
          refineRelevantPredicatesComputer(pPath, pReached);
          pRepeatedCounterexample = false;
          refinedRelevantPredicatesComputer = true;
        }
      }

      lastAbstractions = getRegionsForPath(pPath);
      refinedLastRelevantPredicatesComputer = refinedRelevantPredicatesComputer;
      super.performRefinement(pReached, pPath, pCounterexample, pRepeatedCounterexample);
    }

    private void refineRelevantPredicatesComputer(List<Pair<ARGState, CFANode>> pPath, ARGReachedSet pReached) {
      UnmodifiableReachedSet reached = pReached.asReachedSet();
      Precision oldPrecision = reached.getPrecision(reached.getLastState());
      PredicatePrecision oldPredicatePrecision = Precisions.extractPrecisionByType(oldPrecision, PredicatePrecision.class);

      BlockPartitioning partitioning = predicateCpa.getPartitioning();
      Deque<Block> openBlocks = new ArrayDeque<Block>();
      openBlocks.push(partitioning.getMainBlock());
      for (Pair<ARGState, CFANode> pathElement : pPath) {
        CFANode currentNode = pathElement.getSecond();
        if (partitioning.isCallNode(currentNode)) {
          openBlocks.push(partitioning.getBlockForCallNode(currentNode));
        }

        Collection<AbstractionPredicate> localPreds = oldPredicatePrecision.getPredicates(currentNode);
        for (Block block : openBlocks) {
          for (AbstractionPredicate pred : localPreds) {
            relevantPredicatesComputer.considerPredicateAsRelevant(block, pred);
          }
        }

        while (openBlocks.peek().isReturnNode(currentNode)) {
          openBlocks.pop();
        }
      }

      ((ABMPredicateReducer)predicateCpa.getReducer()).clearCaches();
    }

    @Override
    protected final List<Formula> getFormulasForPath(List<Pair<ARGState, CFANode>> pPath, ARGState initialState) throws CPATransferException {
      // the elements in the path are not expanded, so they contain the path formulas
      // with the wrong indices
      // we need to re-create all path formulas in the flattened ARG

      ssaRenamingTimer.start();
      try {
        return computeBlockFormulas(initialState);

      } finally {
        ssaRenamingTimer.stop();
      }
    }

    private List<Formula> computeBlockFormulas(ARGState pRoot) throws CPATransferException {

      Map<ARGState, PathFormula> formulas = new HashMap<ARGState, PathFormula>();
      List<Formula> abstractionFormulas = Lists.newArrayList();
      Deque<ARGState> todo = new ArrayDeque<ARGState>();

      // initialize
      assert pRoot.getParents().isEmpty();
      formulas.put(pRoot, pfmgr.makeEmptyPathFormula());
      todo.addAll(pRoot.getChildren());

      // iterate over all elements in the ARG with BFS
      outer: while (!todo.isEmpty()) {
        ARGState currentElement = todo.pollFirst();
        if (formulas.containsKey(currentElement)) {
          continue; // already handled
        }

        // collect formulas for current location
        List<PathFormula> currentFormulas = Lists.newArrayListWithExpectedSize(currentElement.getParents().size());
        for (ARGState parentElement : currentElement.getParents()) {
          PathFormula parentFormula = formulas.get(parentElement);
          if (parentFormula == null) {
            // parent not handled yet, re-queue current element
            todo.addLast(currentElement);
            continue outer;

          } else {
            CFAEdge edge = parentElement.getEdgeToChild(currentElement);
            PathFormula currentFormula = pfmgr.makeAnd(parentFormula, edge);
            currentFormulas.add(currentFormula);
          }
        }
        assert currentFormulas.size() >= 1;

        PredicateAbstractState predicateElement = extractStateByType(currentElement, PredicateAbstractState.class);
        if (predicateElement.isAbstractionState()) {
          // abstraction element
          PathFormula currentFormula = getOnlyElement(currentFormulas);
          abstractionFormulas.add(currentFormula.getFormula());

          // start new block with empty formula
          assert todo.isEmpty() : "todo should be empty because of the special ARG structure";
          formulas.clear(); // free some memory

          formulas.put(currentElement, pfmgr.makeEmptyPathFormula(currentFormula));

        } else {
          // merge the formulas
          Iterator<PathFormula> it = currentFormulas.iterator();
          PathFormula currentFormula = it.next();
          while (it.hasNext()) {
            currentFormula = pfmgr.makeOr(currentFormula, it.next());
          }

          formulas.put(currentElement, currentFormula);
        }

        todo.addAll(currentElement.getChildren());
      }
      return abstractionFormulas;
    }
  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    refiner.collectStatistics(pStatsCollection);
  }

  @Override
  protected CounterexampleInfo performRefinementForProperty(AbstractState pSuccessor, CFANode pLoc,
      Proposition pProposition, String pCheckType, boolean pB) throws CPAException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }



  //@Override
 // protected CounterexampleInfo performRefinement1(ARGReachedSet pReached, Path pPath, Proposition pProposition) {
    // TODO Auto-generated method stub
 //   return null;
 // }

}
