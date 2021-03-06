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

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.NestedTimer;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager.RegionCreator;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.ExtendedFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.TheoremProver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.TheoremProver.AllSatResult;
import org.xidian.yk.Operators;

@Options(prefix="cpa.predicate")
public class PredicateAbstractionManager {

  static class Stats {
    public int numCallsAbstraction = 0;
    public int numSymbolicAbstractions = 0;
    public int numSatCheckAbstractions = 0;
    public int numCallsAbstractionCached = 0;
    public final NestedTimer abstractionEnumTime = new NestedTimer(); // outer: solver time, inner: bdd time
    public final Timer abstractionSolveTime = new Timer(); // only the time for solving, not for model enumeration

    public long allSatCount = 0;
    public int maxAllSatCount = 0;

    public int numPathFormulaCoverageChecks = 0;
    public int numEqualPathFormulae = 0;
    public int numSyntacticEntailedPathFormulae = 0;
    public int numSemanticEntailedPathFormulae = 0;
  }

  final Stats stats;

  private final LogManager logger;
  private final ExtendedFormulaManager fmgr;
  private final AbstractionManager amgr;
  private final Solver solver;

  @Option(name="abstraction.cartesian",
      description="whether to use Boolean (false) or Cartesian (true) abstraction")
  private boolean cartesianAbstraction = false;

  @Option(name="abstraction.dumpHardQueries",
      description="dump the abstraction formulas if they took to long")
  private boolean dumpHardAbstractions = false;

  @Option(name="abs.useCache", description="use caching of abstractions")
  private boolean useCache = true;

  private boolean warnedOfCartesianAbstraction = false;

  private final Map<Pair<Formula, Collection<AbstractionPredicate>>, AbstractionFormula> abstractionCache;
  //cache for cartesian abstraction queries. For each predicate, the values
  // are -1: predicate is false, 0: predicate is don't care,
  // 1: predicate is true
  private final Map<Pair<Formula, AbstractionPredicate>, Byte> cartesianAbstractionCache;
  private final Map<Formula, Boolean> feasibilityCache;

  public PredicateAbstractionManager(
      AbstractionManager pAmgr,
      ExtendedFormulaManager pFmgr,
      Solver pSolver,
      Configuration config,
      LogManager pLogger) throws InvalidConfigurationException {

    config.inject(this, PredicateAbstractionManager.class);

    stats = new Stats();
    logger = pLogger;
    fmgr = pFmgr;
    amgr = pAmgr;
    solver = pSolver;

    if (useCache) {
      abstractionCache = new HashMap<Pair<Formula, Collection<AbstractionPredicate>>, AbstractionFormula>();
    } else {
      abstractionCache = null;
    }
    if (useCache && cartesianAbstraction) {
      cartesianAbstractionCache = new HashMap<Pair<Formula, AbstractionPredicate>, Byte>();
      feasibilityCache = new HashMap<Formula, Boolean>();
    } else {
      cartesianAbstractionCache = null;
      feasibilityCache = null;
    }
  }

  /**
   * Abstract post operation.
   */
  public AbstractionFormula buildAbstraction(
      AbstractionFormula abstractionFormula, PathFormula pathFormula,
      Collection<AbstractionPredicate> predicates) {

    stats.numCallsAbstraction++;

//    if (predicates.isEmpty()) {
//      stats.numSymbolicAbstractions++;
//      return makeTrueAbstractionFormula(pathFormula.getFormula());
//    }

    logger.log(Level.ALL, "Old abstraction:", abstractionFormula);
    logger.log(Level.ALL, "Path formula:", pathFormula);
    logger.log(Level.ALL, "Predicates:", predicates);

    Formula absFormula = abstractionFormula.asInstantiatedFormula();
    Formula symbFormula = buildFormula(pathFormula.getFormula());
    Formula f = fmgr.makeAnd(absFormula, symbFormula);

    //从root节点到当前节点的路径公式
    if(Operators.tempEdge.isKeyEdge()){
      Operators.tempKeyFormulas.add(symbFormula);
    }

//    TheoremProver myProver = solver.getTheoremProver();
//    myProver.init();
//    for(Formula f1 : Operators.tempKeyFormulas){
//      myProver.push(f1);
//    }
//   // Operators.time_solve1=System.currentTimeMillis()-Operators.time_solve1;
//    Operators.time_solve=System.currentTimeMillis();
//    Operators.isUnSat=myProver.isUnsat();
//    Operators.time_solve=System.currentTimeMillis()-Operators.time_solve;
//    Operators.time_solve2=System.currentTimeMillis();
//    if(!Operators.isUnSat){
//     try {
//      Operators.model = myProver.getModel();
//      //yangkai 将关键变量的值保存到lastValue中
//      Iterator<String> it=Operators.lastTerms.keySet().iterator();
//      while(it.hasNext()){
//        String next=it.next();
//        Term t=Operators.lastTerms.get(next);
//        AssignableTerm assign = Operators.modelTermToAssign.get(t);
//        if(Operators.model.keySet().contains(assign)){
//          if(!Operators.inputOrRandVar.contains(next)){//当前变量不在inputOrRandVar中
//             Operators.lastValues.put(next, Operators.model.get(assign).toString());
//          }
//         }
//        //System.out.println(t+"="+Operators.model.get(assign));
//      }
////      SSAMap ssa = pathFormula.getSsa();
////      int index = ssa.getIndex("x");
////      Set<AssignableTerm> keyTermSet = Operators.model.delegate1().keySet();
//
//      //System.out.println(Operators.model);
//    } catch (SolverException e) {
//      // TODO Auto-generated catch block
//      e.printStackTrace();
//    }
//    }
    //Operators.time_solve2=System.currentTimeMillis()-Operators.time_solve2;
    //myProver.reset();
    if (predicates.isEmpty()) {
      stats.numSymbolicAbstractions++;
      Operators.time_solve1=System.currentTimeMillis();
      AbstractionFormula ref = makeTrueAbstractionFormula(pathFormula.getFormula());
      Operators.time_solve1=System.currentTimeMillis()-Operators.time_solve1;
      return ref;
    }
    // caching
    Pair<Formula, Collection<AbstractionPredicate>> absKey = null;
    if (useCache) {
      absKey = Pair.of(f, predicates);
      AbstractionFormula result = abstractionCache.get(absKey);

      if (result != null) {
        // create new abstraction object to have a unique abstraction id

        // instantiate the formula with the current indices
        Formula stateFormula = result.asFormula();
        Formula instantiatedFormula = fmgr.instantiate(stateFormula, pathFormula.getSsa());

        result = new AbstractionFormula(result.asRegion(), stateFormula, instantiatedFormula, pathFormula.getFormula());
        logger.log(Level.ALL, "Abstraction was cached, result is", result);
        stats.numCallsAbstractionCached++;
        return result;
      }
    }

    Region abs;
    if (cartesianAbstraction) {
      abs = buildCartesianAbstraction(f, pathFormula.getSsa(), predicates);
    } else {
      abs = buildBooleanAbstraction(f, pathFormula.getSsa(), predicates);
    }

    AbstractionFormula result = makeAbstractionFormula(abs, pathFormula.getSsa(), pathFormula.getFormula());

    if (useCache) {
      abstractionCache.put(absKey, result);
    }

    return result;
  }

  private Region buildCartesianAbstraction(final Formula f, final SSAMap ssa,
      Collection<AbstractionPredicate> predicates) {
    final RegionCreator rmgr = amgr.getRegionCreator();

    stats.abstractionEnumTime.startOuter();

    TheoremProver thmProver = solver.getTheoremProver();
    thmProver.init();
    try {
      thmProver.push(f);

      boolean feasibility;
      if (useCache && feasibilityCache.containsKey(f)) {
        feasibility = feasibilityCache.get(f);

      } else {
        feasibility = !thmProver.isUnsat();
        if (useCache) {
          feasibilityCache.put(f, feasibility);
        }
      }

      if (!feasibility) {
        // abstract post leads to false, we can return immediately
        return rmgr.makeFalse();
      }

      if (!warnedOfCartesianAbstraction && !fmgr.isPurelyConjunctive(f)) {
        logger.log(Level.WARNING, "Using cartesian abstraction when formulas contain disjunctions may be imprecise. This might lead to failing refinements.");
        warnedOfCartesianAbstraction = true;
      }

      try {
        Region absbdd = rmgr.makeTrue();

        // check whether each of the predicate is implied in the next state...

        for (AbstractionPredicate p : predicates) {
          Pair<Formula, AbstractionPredicate> cacheKey = Pair.of(f, p);
          if (useCache && cartesianAbstractionCache.containsKey(cacheKey)) {
            byte predVal = cartesianAbstractionCache.get(cacheKey);

            stats.abstractionEnumTime.getInnerTimer().start();
            Region v = p.getAbstractVariable();
            if (predVal == -1) { // pred is false
              v = rmgr.makeNot(v);
              absbdd = rmgr.makeAnd(absbdd, v);
            } else if (predVal == 1) { // pred is true
              absbdd = rmgr.makeAnd(absbdd, v);
            } else {
              assert predVal == 0 : "predicate value is neither false, true, nor unknown";
            }
            stats.abstractionEnumTime.getInnerTimer().stop();

          } else {
            logger.log(Level.ALL, "DEBUG_1",
                "CHECKING VALUE OF PREDICATE: ", p.getSymbolicAtom());

            // instantiate the definition of the predicate
            Formula predTrue = fmgr.instantiate(p.getSymbolicAtom(), ssa);
            Formula predFalse = fmgr.makeNot(predTrue);

            // check whether this predicate has a truth value in the next
            // state
            byte predVal = 0; // pred is neither true nor false

            thmProver.push(predFalse);
            boolean isTrue = thmProver.isUnsat();
            thmProver.pop();

            if (isTrue) {
              stats.abstractionEnumTime.getInnerTimer().start();
              Region v = p.getAbstractVariable();
              absbdd = rmgr.makeAnd(absbdd, v);
              stats.abstractionEnumTime.getInnerTimer().stop();

              predVal = 1;
            } else {
              // check whether it's false...
              thmProver.push(predTrue);
              boolean isFalse = thmProver.isUnsat();
              thmProver.pop();

              if (isFalse) {
                stats.abstractionEnumTime.getInnerTimer().start();
                Region v = p.getAbstractVariable();
                v = rmgr.makeNot(v);
                absbdd = rmgr.makeAnd(absbdd, v);
                stats.abstractionEnumTime.getInnerTimer().stop();

                predVal = -1;
              }
            }

            if (useCache) {
              cartesianAbstractionCache.put(cacheKey, predVal);
            }
          }
        }

        return absbdd;

      } finally {
        thmProver.pop();
      }

    } finally {
      thmProver.reset();

      stats.abstractionEnumTime.stopOuter();
    }
  }

  private Formula buildFormula(Formula symbFormula) {

    if (fmgr.useBitwiseAxioms()) {
      Formula bitwiseAxioms = fmgr.getBitwiseAxioms(symbFormula);
      if (!bitwiseAxioms.isTrue()) {
        symbFormula = fmgr.makeAnd(symbFormula, bitwiseAxioms);

        logger.log(Level.ALL, "DEBUG_3", "ADDED BITWISE AXIOMS:", bitwiseAxioms);
      }
    }

    return symbFormula;
  }

  private Region buildBooleanAbstraction(Formula f, SSAMap ssa,
      Collection<AbstractionPredicate> predicates) {

    // first, create the new formula corresponding to
    // (symbFormula & edges from e to succ)
    // TODO - at the moment, we assume that all the edges connecting e and
    // succ have no statement or assertion attached (i.e. they are just
    // return edges or gotos). This might need to change in the future!!
    // (So, for now we don't need to to anything...)

    // build the definition of the predicates, and instantiate them
    // also collect all predicate variables so that the solver knows for which
    // variables we want to have the satisfying assignments
    Formula predDef = fmgr.makeTrue();
    List<Formula> predVars = new ArrayList<Formula>(predicates.size());

    for (AbstractionPredicate p : predicates) {
      // get propositional variable and definition of predicate
      Formula var = p.getSymbolicVariable();
      Formula def = p.getSymbolicAtom();
      if (def.isFalse()) {
        continue;
      }
      def = fmgr.instantiate(def, ssa);

      // build the formula (var <-> def) and add it to the list of definitions
      Formula equiv = fmgr.makeEquivalence(var, def);
      predDef = fmgr.makeAnd(predDef, equiv);

      predVars.add(var);
    }

    // the formula is (abstractionFormula & pathFormula & predDef)
    Formula fm = fmgr.makeAnd(f, predDef);
    Region result;

    if (predVars.isEmpty()) {
      stats.numSatCheckAbstractions++;

      stats.abstractionSolveTime.start();
      boolean satResult = !solver.isUnsat(fm);
      stats.abstractionSolveTime.stop();

      RegionCreator rmgr = amgr.getRegionCreator();

      result = (satResult) ? rmgr.makeTrue() : rmgr.makeFalse();

    } else {
      logger.log(Level.ALL, "COMPUTING ALL-SMT ON FORMULA: ", fm);
      TheoremProver thmProver = solver.getTheoremProver();
      AllSatResult allSatResult = thmProver.allSat(fm, predVars, amgr.getRegionCreator(),
          stats.abstractionSolveTime, stats.abstractionEnumTime);
      result = allSatResult.getResult();

      // update statistics
      int numModels = allSatResult.getCount();
      if (numModels < Integer.MAX_VALUE) {
        stats.maxAllSatCount = Math.max(numModels, stats.maxAllSatCount);
        stats.allSatCount += numModels;
      }
    }

    if (dumpHardAbstractions) {
      // we want to dump "hard" problems...
      long abstractionTime = stats.abstractionSolveTime.getLengthOfLastInterval()
                            + stats.abstractionEnumTime.getLengthOfLastOuterInterval();

      if (abstractionTime > 10000) {
        File dumpFile;

        dumpFile = fmgr.formatFormulaOutputFile("abstraction", stats.numCallsAbstraction, "input", 0);
        fmgr.dumpFormulaToFile(f, dumpFile);

        dumpFile = fmgr.formatFormulaOutputFile("abstraction", stats.numCallsAbstraction, "predDef", 0);
        fmgr.dumpFormulaToFile(predDef, dumpFile);

        dumpFile = fmgr.formatFormulaOutputFile("abstraction", stats.numCallsAbstraction, "predVars", 0);
        fmgr.printFormulasToFile(predVars, dumpFile);
      }
    }

    logger.log(Level.ALL, "Abstraction computed, result is", result);
    return result;
  }

  /**
   * Checks if a1 => a2
   */
  public boolean checkCoverage(AbstractionFormula a1, AbstractionFormula a2) {
    return amgr.entails(a1.asRegion(), a2.asRegion());
  }

  /**
   * Checks if (a1 & p1) => a2
   */
  public boolean checkCoverage(AbstractionFormula a1, PathFormula p1, AbstractionFormula a2) {
    Formula absFormula = a1.asInstantiatedFormula();
    Formula symbFormula = buildFormula(p1.getFormula());
    Formula a = fmgr.makeAnd(absFormula, symbFormula);

    // get formula of a2 with the indices of p1
    Formula b = fmgr.instantiate(a2.asFormula(), p1.getSsa());

    return solver.implies(a, b);
  }

  /**
   * Checks whether a1.getFormula() => a2.getFormula() and whether the a1.getSsa()(v) <= a2.getSsa()(v) for all v
   */
  public boolean checkCoverage(PathFormula a1, PathFormula a2, PathFormulaManager pfmgr) {
    stats.numPathFormulaCoverageChecks++;

    //handle common special case more efficiently
    if (a1.equals(a2)) {
      stats.numEqualPathFormulae++;
      return true;
    }

    //check ssa maps
    SSAMap map1 = a1.getSsa();
    SSAMap map2 = a2.getSsa();
    for (String var : map1.allVariables()) {
     if (map2.getIndex(var) < map1.getIndex(var)) {
       return false;
     }
    }

    //merge path formulae
    PathFormula mergedPathFormulae = pfmgr.makeOr(a1, a2);

    //quick syntactic check
    Formula leftFormula = fmgr.getArguments(mergedPathFormulae.getFormula())[0];
    Formula rightFormula = a2.getFormula();
    if (fmgr.checkSyntacticEntails(leftFormula, rightFormula)) {
      stats.numSyntacticEntailedPathFormulae++;
      return true;
    }


    //check formulae
    if (!solver.implies(mergedPathFormulae.getFormula(), a2.getFormula())) {
      return false;
    }
    stats.numSemanticEntailedPathFormulae++;

    return true;
  }

  /**
   * Checks if an abstraction formula and a pathFormula are unsatisfiable.
   * @param pAbstractionFormula the abstraction formula
   * @param pPathFormula the path formula
   * @return unsat(pAbstractionFormula & pPathFormula)
   */
  public boolean unsat(AbstractionFormula abstractionFormula, PathFormula pathFormula) {
    Formula absFormula = abstractionFormula.asInstantiatedFormula();
    Formula symbFormula = buildFormula(pathFormula.getFormula());
    Formula f = fmgr.makeAnd(absFormula, symbFormula);
    logger.log(Level.ALL, "Checking satisfiability of formula", f);

    return solver.isUnsat(f);
  }

  public AbstractionFormula makeTrueAbstractionFormula(Formula pPreviousBlockFormula) {
    if (pPreviousBlockFormula == null) {
      pPreviousBlockFormula = fmgr.makeTrue();
    }
    //System.out.println("pPreviousBlockFormula=>"+pPreviousBlockFormula);
    return new AbstractionFormula(amgr.getRegionCreator().makeTrue(), fmgr.makeTrue(), fmgr.makeTrue(), pPreviousBlockFormula);
  }

  private AbstractionFormula makeAbstractionFormula(Region abs, SSAMap ssaMap, Formula blockFormula) {
    Formula symbolicAbs = amgr.toConcrete(abs);
    Formula instantiatedSymbolicAbs = fmgr.instantiate(symbolicAbs, ssaMap);

    return new AbstractionFormula(abs, symbolicAbs, instantiatedSymbolicAbs, blockFormula);
  }

  /**
   * Remove a set of predicates from an abstraction.
   * @param oldAbstraction The abstraction to start from.
   * @param removePredicates The predicate to remove.
   * @param ssaMap The SSAMap to use for instantiating the new abstraction.
   * @return A new abstraction similar to the old one without the predicates.
   */
  public AbstractionFormula reduce(AbstractionFormula oldAbstraction,
      Collection<AbstractionPredicate> removePredicates, SSAMap ssaMap) {
    RegionCreator rmgr = amgr.getRegionCreator();

    Region newRegion = oldAbstraction.asRegion();
    for (AbstractionPredicate predicate : removePredicates) {
      newRegion = rmgr.makeExists(newRegion, predicate.getAbstractVariable());
    }

    return makeAbstractionFormula(newRegion, ssaMap, oldAbstraction.getBlockFormula());
  }

  /**
   * Extend an abstraction by a set of predicates.
   * @param reducedAbstraction The abstraction to extend.
   * @param sourceAbstraction The abstraction where to take the predicates from.
   * @param relevantPredicates The predicates to add.
   * @param newSSA The SSAMap to use for instantiating the new abstraction.
   * @return A new abstraction similar to the old one with some more predicates.
   */
  public AbstractionFormula expand(AbstractionFormula reducedAbstraction, AbstractionFormula sourceAbstraction,
      Collection<AbstractionPredicate> relevantPredicates, SSAMap newSSA) {
    RegionCreator rmgr = amgr.getRegionCreator();

    Region removedInformationRegion = sourceAbstraction.asRegion();
    for (AbstractionPredicate predicate : relevantPredicates) {
      removedInformationRegion = rmgr.makeExists(removedInformationRegion,
                                                 predicate.getAbstractVariable());
    }

    Region expandedRegion = rmgr.makeAnd(reducedAbstraction.asRegion(), removedInformationRegion);

    return makeAbstractionFormula(expandedRegion, newSSA, reducedAbstraction.getBlockFormula());
  }

  // delegate methods

  public Collection<AbstractionPredicate> extractPredicates(Region pRegion) {
    return amgr.extractPredicates(pRegion);
  }
}
