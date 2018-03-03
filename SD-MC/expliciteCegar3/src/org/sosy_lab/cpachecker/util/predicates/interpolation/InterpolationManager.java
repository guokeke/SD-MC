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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;

import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Timer;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.configuration.TimeSpanOption;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CArrayType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException.Reason;
import org.sosy_lab.cpachecker.exceptions.SolverException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.globalinfo.SSAMapInfo;
import org.sosy_lab.cpachecker.util.predicates.CSIsatInterpolatingProver;
import org.sosy_lab.cpachecker.util.predicates.ExtendedFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.FormulaManagerFactory;
import org.sosy_lab.cpachecker.util.predicates.Model;
import org.sosy_lab.cpachecker.util.predicates.Model.AssignableTerm;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.InterpolatingTheoremProver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.TheoremProver;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolFormula;
import org.xidian.cpachecker.dz.Proposition;
import org.xidian.cpachecker.dz.Algorithm.ArrayCheckAlgorithm;
import org.xidian.cpachecker.dz.proposition.PropositionInfo;
import org.xidian.yk.Operators;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multiset;
import com.google.common.collect.Sets;
import com.google.common.util.concurrent.ThreadFactoryBuilder;
import com.songstan.ltl_trans.method.Transition;

import de.uni_freiburg.informatik.ultimate.logic.Term;

@Options(prefix = "cpa.predicate.refinement")
public abstract class InterpolationManager<I> {

  static class Stats {

    private final Timer cexAnalysisTimer = new Timer();
    private final Timer cexAnalysisSolverTimer = new Timer();
    private final Timer cexAnalysisGetUsefulBlocksTimer = new Timer();
    private final Timer interpolantVerificationTimer = new Timer();

    void printStatistics(PrintStream out, Result result, ReachedSet reached) {
      out.println("  Counterexample analysis:        " + cexAnalysisTimer + " (Max: " + cexAnalysisTimer.printMaxTime()
          + ", Calls: " + cexAnalysisTimer.getNumberOfIntervals() + ")");
      if (cexAnalysisGetUsefulBlocksTimer.getMaxTime() != 0) {
        out.println("    Cex.focusing:                 " + cexAnalysisGetUsefulBlocksTimer + " (Max: "
            + cexAnalysisGetUsefulBlocksTimer.printMaxTime() + ")");
      }
      out.println("    Solving time only:            " + cexAnalysisSolverTimer + " (Max: "
          + cexAnalysisSolverTimer.printMaxTime() + ", Calls: " + cexAnalysisSolverTimer.getNumberOfIntervals() + ")");
      if (interpolantVerificationTimer.getNumberOfIntervals() > 0) {
        out.println("    Interpolant verification:     " + interpolantVerificationTimer);
      }
    }
  }

  private String var = "";
  private static boolean entryMain = false;
  final Stats stats = new Stats();
  protected final LogManager logger;
  //private final Configuration config;
  protected final ExtendedFormulaManager fmgr;
  protected final PathFormulaManager pmgr;
  private final Solver solver;

  private final InterpolatingTheoremProver<?> firstItpProver;
  private final InterpolatingTheoremProver<?> secondItpProver;

  @Option(name = "interpolatingProver", toUppercase = true, values = { "DEFAULT", "CSISAT" },
      description = "Which interpolating solver to use for interpolant generation?\n"
          + "DEFAULT means to use the solver used for everything else as well.")
  private String whichItpProver = "DEFAULT";

  @Option(description = "apply deletion-filter to the abstract counterexample, to get "
      + "a minimal set of blocks, before applying interpolation-based refinement")
  private boolean getUsefulBlocks = false;

  @Option(name = "shortestCexTrace",
      description = "use incremental search in counterexample analysis, "
          + "to find the minimal infeasible prefix")
  private boolean shortestTrace = false;

  @Option(name = "shortestCexTraceUseSuffix",
      description = "if shortestCexTrace is used, "
          + "start from the end with the incremental search")
  private boolean useSuffix = false;

  @Option(name = "shortestCexTraceZigZag",
      description = "if shortestCexTrace is used, "
          + "alternatingly search from start and end of the trace")
  private boolean useZigZag = false;

  @Option(name = "addWellScopedPredicates",
      description = "refinement will try to build 'well-scoped' predicates, "
          + "by cutting spurious traces as explained in Section 5.2 of the paper "
          + "'Abstractions From Proofs'\n(this does not work with function inlining).\n"
          + "THIS FEATURE IS CURRENTLY NOT AVAILABLE. ")
  private boolean wellScopedPredicates = false;

  @Option(description = "dump all interpolation problems")
  private boolean dumpInterpolationProblems = false;

  @Option(description = "verify if the interpolants fulfill the interpolant properties")
  private boolean verifyInterpolants = false;

  @Option(name = "timelimit",
      description = "time limit for refinement (use milliseconds or specify a unit; 0 for infinite)")
  @TimeSpanOption(codeUnit = TimeUnit.MILLISECONDS,
      defaultUserUnit = TimeUnit.MILLISECONDS,
      min = 0)
  private long itpTimeLimit = 0;

  @Option(name = "changesolverontimeout",
      description = "try again with a second solver if refinement timed out")
  private boolean changeItpSolveOTF = false;

  @Option(description = "skip refinement if input formula is larger than "
      + "this amount of bytes (ignored if 0)")
  private int maxRefinementSize = 0;

  private final ExecutorService executor;
  private FormulaManagerFactory pFmgrFactory;

  public InterpolationManager(
      ExtendedFormulaManager pFmgr,
      PathFormulaManager pPmgr,
      Solver pSolver,
      FormulaManagerFactory pFmgrFactory,
      Configuration config,
      LogManager pLogger) throws InvalidConfigurationException {
    config.inject(this, InterpolationManager.class);

    logger = pLogger;
    fmgr = pFmgr;
    pmgr = pPmgr;
    solver = pSolver;
    this.pFmgrFactory = pFmgrFactory;

    // create solvers
    if (whichItpProver.equals("CSISAT")) {
      firstItpProver = new CSIsatInterpolatingProver(fmgr, logger);
    } else {
      assert whichItpProver.equals("DEFAULT");
      firstItpProver = pFmgrFactory.createInterpolatingTheoremProver(false);
    }

    if (changeItpSolveOTF) {
      if (whichItpProver.equals("CSISAT")) {
        secondItpProver = pFmgrFactory.createInterpolatingTheoremProver(false);
      } else {
        assert whichItpProver.equals("DEFAULT");
        secondItpProver = new CSIsatInterpolatingProver(fmgr, logger);
      }
    } else {
      secondItpProver = null;
    }

    if (itpTimeLimit == 0) {
      executor = null;
    } else {
      // important to use daemon threads here, because we never have the chance to stop the executor
      executor = Executors.newSingleThreadExecutor(new ThreadFactoryBuilder().setDaemon(true).build());
    }

    if (wellScopedPredicates) { throw new InvalidConfigurationException("wellScopePredicates are currently disabled"); }
    //    if (inlineFunctions && wellScopedPredicates) {
    //      logger.log(Level.WARNING, "Well scoped predicates not possible with function inlining, disabling them.");
    //      wellScopedPredicates = false;
    //    }
  }

  public String dumpCounterexample(CounterexampleTraceInfo<I> cex) {
    return fmgr.dumpFormula(fmgr.makeConjunction(cex.getCounterExampleFormulas()));
  }

  /**
   * Counterexample analysis and predicate discovery.
   * This method is just an helper to delegate the actual work
   * This is used to detect timeouts for interpolation
   *
   * @param pFormulas the formulas for the path
   * @param elementsOnPath the ARGElements on the path (may be empty if no branching information is required)
   * @throws CPAException
   * @throws InterruptedException
   */
  public CounterexampleTraceInfo<I> buildCounterexampleTrace(
      final List<Formula> pFormulas,
      final Set<ARGState> elementsOnPath) throws CPAException, InterruptedException {

    // if we don't want to limit the time given to the solver
    if (itpTimeLimit == 0) { return buildCounterexampleTraceWithSpecifiedItp(pFormulas, elementsOnPath, firstItpProver); }

    assert executor != null;

    // how many times is the problem tried to be solved so far?
    int noOfTries = 0;

    while (true) {
      final InterpolatingTheoremProver<?> currentItpProver =
          (noOfTries == 0) ? firstItpProver : secondItpProver;

      Callable<CounterexampleTraceInfo<I>> tc = new Callable<CounterexampleTraceInfo<I>>() {

        @Override
        public CounterexampleTraceInfo<I> call() throws CPAException, InterruptedException {
          return buildCounterexampleTraceWithSpecifiedItp(pFormulas, elementsOnPath, currentItpProver);
        }
      };

      Future<CounterexampleTraceInfo<I>> future = executor.submit(tc);

      try {
        // here we get the result of the post computation but there is a time limit
        // given to complete the task specified by timeLimit
        return future.get(itpTimeLimit, TimeUnit.MILLISECONDS);

      } catch (TimeoutException e) {
        // if first try failed and changeItpSolveOTF enabled try the alternative solver
        if (changeItpSolveOTF && noOfTries == 0) {
          logger.log(Level.WARNING, "SMT-solver timed out during interpolation process, trying next solver.");
          noOfTries++;

        } else {
          logger.log(Level.SEVERE, "SMT-solver timed out during interpolation process");
          throw new RefinementFailedException(Reason.TIMEOUT, null);
        }

      } catch (ExecutionException e) {
        Throwable t = e.getCause();
        Throwables.propagateIfPossible(t, CPAException.class, InterruptedException.class);

        throw new UnexpectedCheckedException("interpolation", t);
      }
    }
  }

  public CounterexampleTraceInfo<I> buildCounterexampleTraceForPointer(final List<Formula> pFormulas,
      AbstractState pSuccessor,
      final CFANode loc, Proposition pProposition, boolean pB) throws CPAException, InterruptedException {
    return buildCounterexampleTraceWithSpecifiedItpForPointer(pFormulas, (ARGState) pSuccessor, loc, firstItpProver,
        pProposition, pB);
  }

  public CounterexampleTraceInfo<I> buildCounterexampleTraceForSimpleProperty(final List<Formula> pFormulas,
      AbstractState pSuccessor,
      final CFANode loc, Proposition pProposition, boolean pB) throws CPAException, InterruptedException {
    return buildCounterexampleTraceWithSpecifiedItpForSimpleProperty(pFormulas, (ARGState) pSuccessor, loc,
        firstItpProver,
        pProposition, pB);
  }

  public CounterexampleTraceInfo<I> buildCounterexampleTraceForArray(final List<Formula> pFormulas,
      AbstractState pSuccessor,
      final CFANode loc, Proposition pProposition, boolean pB) throws CPAException, InterruptedException {
    return buildCounterexampleTraceWithSpecifiedItpForArray(pFormulas, (ARGState) pSuccessor, loc, firstItpProver,
        pProposition, pB);
  }

  private <T> CounterexampleTraceInfo<I> buildCounterexampleTraceWithSpecifiedItpForPointer(List<Formula> f,
      ARGState successor,
      CFANode loc, InterpolatingTheoremProver<T> pFirstItpProver, Proposition proposition, boolean b)
      throws InterruptedException, RefinementFailedException, CPATransferException {


    logger.log(Level.FINEST, "Building counterexample trace");
    stats.cexAnalysisTimer.start();
    pFirstItpProver.init();
    //List<Formula> f1 = new ArrayList<Formula>(f);
    ARGState sucParent = successor.getParents().iterator().next();
    try {
      // Final adjustments to the list of formulas
      CFAEdge addEdge = null;
      CFAEdge edgeSuc = sucParent.getEdgeToChild(successor);
      Map<Pair<String, String>, String> propositions = proposition.getPropositions();
      Iterator<Pair<String, String>> iterator = propositions.keySet().iterator();
      Pair<String, String> rp = propositions.keySet().iterator().next();
      String first = propositions.get(rp);
      Transition transition = successor.getTransition();
      String funcname = edgeSuc.getPredecessor().getFunctionName();
      PathFormula sucPPath = null;
      PathFormula pFSuc = null;
      sucPPath = sucParent.getPathFormula();
      if (edgeSuc instanceof CAssumeEdge) {//遇到分支
        Proposition pp = sucParent.getProposition();
        Iterator<Pair<String, String>> it = pp.getPropositions().keySet().iterator();
        CFAEdge pEdge = null;
        while (it.hasNext()) {
          Pair<String, String> p = it.next();
          if (p.getFirst().equals("d") || p.getFirst().equals("!d")) {
            pEdge = proposition.getPropEdges().get(p);
            break;
          }
        }
        int spurious = 0;
        while (iterator.hasNext()) {
          Pair<String, String> next = iterator.next();
          if (next.getFirst().equals("r")) {
            rp = next;
            break;
          }
        }
        String second = rp.getSecond();
        var = second.substring(0, second.indexOf("==")).trim();
        int count = 0;
        spurious = 0;
        String curTerm = transition.getLabel().trim();
        curTerm = curTerm.replaceAll("[\\(|\\)| ]", "");

        if (first.equals("Global") || first.equals(edgeSuc.getPredecessor().getFunctionName())) {
          curTerm = curTerm.replaceAll("true", "*");
          boolean myjudge = false;
          myjudge = CFAUtils.judge(edgeSuc, var);
          if(!myjudge&&curTerm.contains("r")){
             successor.setTransition(null);
          }
          else if(myjudge){
            count = generateOneStepFormula(f, sucPPath, edgeSuc, transition, proposition);
            spurious= checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
            if(spurious==1){
              successor.setTransition(null);
            }

          }
//          count = generateOneStepFormula(f, sucPPath, edgeSuc, transition, proposition);
//          spurious = checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
//          if (spurious == 1) { //f1 is false
//            successor.setTransition(null);
//          }
//          else {
//            //处理命题r
//
//            curTerm = curTerm.replaceAll("true", "*");
//            boolean myjudge = false;
//            myjudge = CFAUtils.judge(edgeSuc, var);
//            if (curTerm.contains("!r")) {
//              if (myjudge) {
//                successor.setTransition(null);
//              }
//            }
//            else if (curTerm.contains("r")&&!curTerm.contains("!r")) {
//              if (!myjudge) {
//                successor.setTransition(null);
//              }
//            }
//          }
        }
        else {
          String curTerms[] = curTerm.split("&&");
          for (int i = 0; i < curTerms.length; i++) {
            String subTerm = curTerms[i].trim();
            if (!subTerm.equals("true") && !subTerm.startsWith("!")) {
              successor.setTransition(null);
              break;
            }
          }
        }

        CounterexampleTraceInfo<I> info1 = new CounterexampleTraceInfo<I>();
        while (count != 0) {
          f.remove(f.size() - 1);
          count--;
        }
        return info1;
      }
      if (edgeSuc instanceof CStatementEdge) {//eg: if " int *x=malloc() ", then x!=0 ;
        CStatement s = ((CStatementEdge) edgeSuc).getStatement();
        if (s instanceof CFunctionCallAssignmentStatement) {
          CFunctionCallExpression right = ((CFunctionCallAssignmentStatement) s).getRightHandSide();
          if (right.getFunctionNameExpression().toASTString().contains("alloc")) {
            CExpression left = ((CFunctionCallAssignmentStatement) s).getLeftHandSide();
            String l = left.toASTString();
            String func = edgeSuc.getSuccessor().getFunctionName();
            l = l + "=" + "0x0001;";
            String addinfo = "int " + func + "(){" + l + "}";
            ParseResult myString;
            try {
              myString = PropositionInfo.parser.parseString(addinfo);
              Map<String, FunctionEntryNode> fn = myString.getFunctions();
              CFANode node = fn.get(func);
              while (node.getNumLeavingEdges() != 0) {
                CFAEdge e = node.getLeavingEdge(0);
                if (e.getRawStatement().equals(l)) {
                  addEdge = e;
                  break;
                }
                node = e.getSuccessor();
              }
            } catch (org.sosy_lab.cpachecker.exceptions.ParserException e1) {
              // TODO Auto-generated catch block
              e1.printStackTrace();
            }
          }
        }
      }
//      if (addEdge == null && (edgeSuc.getDescription().contains("<<") || edgeSuc.getDescription().contains(">>"))) {
//        String des = edgeSuc.getDescription().toString();
//        List<String> list = GlobalInfo.getInstance().getMyString(edgeSuc);
//        //System.out.println("list=" + list);
//        for (String s : list) {
//          while (des.contains(">> " + s)) {
//            String tmp =
//                des.substring(0, des.indexOf(">> " + s)) + des.substring(des.indexOf(">> " + s) + s.length() + 3);
//            des = tmp;
//          }
//          while (des.contains(">> (" + s + ")")) {
//            String tmp =
//                des.substring(0, des.indexOf(">> (" + s + ")"))
//                    + des.substring(des.indexOf(">> (" + s + ")") + s.length() + 5);
//            des = tmp;
//          }
//          while (des.contains("<< " + s)) {
//            String tmp =
//                des.substring(0, des.indexOf("<< " + s)) + des.substring(des.indexOf("<< " + s) + s.length() + 3);
//            des = tmp;
//          }
//          while (des.contains("<< (" + s + ")")) {
//            String tmp =
//                des.substring(0, des.indexOf("<< (" + s + ")"))
//                    + des.substring(des.indexOf("<< (" + s + ")") + s.length() + 5);
//            des = tmp;
//          }
//        }
//        // des=des.replaceAll("<<"," ");
//        // des=des.replaceAll(">>"," ");
//        if (des.contains("=")) {
//
//          String func = edgeSuc.getSuccessor().getFunctionName();
//          // exp=exp.substring(0,exp.indexOf("="))+"=0x0001;";
//          String addinfo = "int " + func + "(){" + des + "}";
//          ParseResult myString;
//          try {
//            myString = PropositionInfo.parser.parseString(addinfo);
//            Map<String, FunctionEntryNode> fn = myString.getFunctions();
//            CFANode node = fn.get(func);
//            while (node.getNumLeavingEdges() != 0) {
//              CFAEdge e = node.getLeavingEdge(0);
//              if (e.getRawStatement().equals(des)) {
//                addEdge = e;
//                break;
//              }
//              node = e.getSuccessor();
//            }
//          } catch (org.sosy_lab.cpachecker.exceptions.ParserException e1) {
//            // TODO Auto-generated catch block
//            e1.printStackTrace();
//          }
//
//        }
//      }
      Multiset<String> tmpset=SSAMapInfo.getInstance().getVars();
      if (addEdge != null){
         pFSuc = pmgr.makeAnd1(sucPPath, addEdge);
       }
       else{
         pFSuc = pmgr.makeAnd1(sucPPath, edgeSuc);
       }
       if (!pFSuc.getFormula().isTrue())
         f.add(pFSuc.getFormula());
      if (fmgr.useBitwiseAxioms()) {
        addBitwiseAxioms(f);
      }
      //f = Collections.unmodifiableList(f);
      logger.log(Level.ALL, "Counterexample trace formulas:", f);

      // now f is the DAG formula which is satisfiable iff there is a
      // concrete counterexample


      // Check if refinement problem is not too big
      if (maxRefinementSize > 0) {
        int size = fmgr.dumpFormula(fmgr.makeConjunction(f)).length();
        if (size > maxRefinementSize) {
          logger.log(Level.FINEST, "Skipping refinement because input formula is", size, "bytes large.");
          throw new RefinementFailedException(Reason.TooMuchUnrolling, null);
        }
      }


      // Check feasibility of counterexample
      logger.log(Level.FINEST, "Checking feasibility of counterexample trace");
      stats.cexAnalysisSolverTimer.start();

      //boolean spurious = false;
      List<T> itpGroupsIds;
      Proposition p = new Proposition();
      //int spur=0;
      try {

        if (shortestTrace && getUsefulBlocks) {

          //f = Collections.unmodifiableList(getUsefulBlocks(f, useSuffix, useZigZag));
        }

        if (dumpInterpolationProblems) {
          dumpInterpolationProblem(f);
        }

        // initialize all interpolation group ids with "null"
        itpGroupsIds = new ArrayList<T>(Collections.<T> nCopies(f.size(), null));

        /* if(b){
           if (getUsefulBlocks || !shortestTrace) {
             spurious = checkInfeasibilityOfFullTrace(f, itpGroupsIds, pFirstItpProver);

           } else {
             spurious = checkInfeasabilityOfShortestTrace(f, itpGroupsIds, pFirstItpProver);
           }
         }
         else{
           spurious=false;
         }*/

      } finally {
        stats.cexAnalysisSolverTimer.stop();
      }
      //logger.log(Level.FINEST, "Counterexample trace is", (spurious ? "infeasible" : "feasible"));
      CounterexampleTraceInfo<I> info = new CounterexampleTraceInfo<I>();

      if (!entryMain) {
        funcname = edgeSuc.getPredecessor().getFunctionName();
        if (funcname.equals("main") && edgeSuc.getDescription().equals("Function start dummy edge")) {
          entryMain = true;
        }
      }
      String curTerm = transition.getLabel().trim();
      curTerm = curTerm.replaceAll("[\\(|\\)| ]", "");
      if (entryMain) {
        while (iterator.hasNext()) {
          Pair<String, String> next = iterator.next();
          if (next.getFirst().equals("r")) {
            rp = next;
            break;
          }
        }
        String second = rp.getSecond();
        var = second.substring(0, second.indexOf("==")).trim();
        int count = 0;
        int spu = 0;
        if (first.equals("Global") || first.equals(edgeSuc.getPredecessor().getFunctionName())) {
          String left = "";
          //Pair<String, String> isR = sucPro.keySet().iterator().next();
          if ((edgeSuc instanceof CStatementEdge)) {
            if (((CStatementEdge) edgeSuc).getStatement() instanceof CExpressionAssignmentStatement) {
              left = ((CStatementEdge) edgeSuc).getStatement().toASTString();
              left = left.substring(0, left.indexOf("=")).trim();
              if (left.equals(var)) {
                if(!curTerm.equals("true")&&!CFAUtils.judge(edgeSuc, var)){
                  successor.setTransition(null);
                  return info;
                }
            }
            }
          }

          //
        //处理命题r
          curTerm = curTerm.replaceAll("true", "*");
          boolean myjudge = false;
          int i=1;
          if(edgeSuc.getDescription().contains("link"))
            i=i-1;
          myjudge = CFAUtils.judge(edgeSuc, var);
          if(!myjudge&&curTerm.contains("r")){
             successor.setTransition(null);
          }
          else if(myjudge){
            count = generateOneStepFormula(f, pFSuc, edgeSuc, transition, proposition);
            spu = checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
            if(spu==1){
              successor.setTransition(null);
            }

          }
          //
//          if (spu == 1) { //f1 is false
//
//          }
//          else {
//
//            if (curTerm.contains("!r")) {
//              if (myjudge) {
//                successor.setTransition(null);
//              }
//            }
//            else if (curTerm.contains("r")&&!curTerm.contains("!r")) {
//              if (!myjudge) {
//                successor.setTransition(null);
//              }
//            }
//          }
        }
        else {
          String curTerms[] = curTerm.split("&&");
          for (int i = 0; i < curTerms.length; i++) {
            String subTerm = curTerms[i].trim();
            if (!subTerm.equals("true") && !subTerm.startsWith("!")) {
              successor.setTransition(null);
              break;
            }
          }
        }
        while (count != 0) {
          f.remove(f.size() - 1);
          count--;
        }
      }
      else {
        String curTerms[] = curTerm.split("&&");
        for (int i = 0; i < curTerms.length; i++) {
          String subTerm = curTerms[i].trim();
          if (!subTerm.equals("true") && !subTerm.startsWith("!")) {
            successor.setTransition(null);
            break;
          }
        }
      }
      return info;
    } finally {
      pFirstItpProver.reset();
      stats.cexAnalysisTimer.stop();
    }

  }

  private <T> CounterexampleTraceInfo<I> buildCounterexampleTraceWithSpecifiedItpForSimpleProperty(List<Formula> f,
      ARGState successor,
      CFANode loc, InterpolatingTheoremProver<T> pFirstItpProver, Proposition proposition, boolean b)
      throws InterruptedException, RefinementFailedException, CPATransferException {


    logger.log(Level.FINEST, "Building counterexample trace");
    stats.cexAnalysisTimer.start();
    pFirstItpProver.init();
    //List<Formula> f1 = null;
    ARGState sucParent = successor.getParents().iterator().next();
    //String varFunction = proposition.getPropositions().values().iterator().next();
    try {
      // Final adjustments to the list of formulas
      int count = 0;
      CFAEdge addEdge = null;
      CFAEdge edgeSuc = sucParent.getEdgeToChild(successor);
      PathFormula sucPPath = null;
      PathFormula pFSuc = null;
      Map<Pair<String, String>, String> propositions = proposition.getPropositions();
      //Iterator<Pair<String, String>> iterator = propositions.keySet().iterator();
      Pair<String, String> rp = propositions.keySet().iterator().next();
      String first = propositions.get(rp);
      Transition transition = successor.getTransition();
      String curTerm = transition.getLabel().trim();
      curTerm = curTerm.replaceAll("[\\(|\\)| ]", "");
      sucPPath = sucParent.getPathFormula();
      if (edgeSuc instanceof CAssumeEdge) {//遇到分支
        //f1 = new ArrayList<Formula>(f);
//        if (edgeSuc.isKeyEdge()){
//          // edgeSuc = addEdge;
//           pFSuc = pmgr.makeAnd1(sucPPath, edgeSuc);
//           f.add(pFSuc.getFormula());
//         }

        //Proposition pp = sucParent.getProposition();
        //Iterator<Pair<String, String>> it = pp.getPropositions().keySet().iterator();
        int spurious = 0;//checkInfeasibilityOfFullTrace1(f1, pFirstItpProver);
        /*if (spurious == 1) {
          CounterexampleTraceInfo<I> info1 = new CounterexampleTraceInfo<I>();
          info1.setProposition(pp);
          info1.setSpurious(true);
          return info1;
        }*/
       // else {
          if (first.equals("Global") || first.equals(edgeSuc.getPredecessor().getFunctionName())) {
            count = generateOneStepFormula(f, sucPPath, edgeSuc, transition, proposition);

            spurious = checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
            if (spurious == 1) { //f1 is false
              Operators.isUnSat=true;
              successor.setTransition(null);
            }
            else{

              Operators.isUnSat=false;
              try {
                Operators.model = pFirstItpProver.getModel();
              } catch (SolverException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
              }
              Iterator<String> it=Operators.lastTerms.keySet().iterator();
              while(it.hasNext()){
                String next=it.next();
                Term t=Operators.lastTerms.get(next);
                AssignableTerm assign = Operators.modelTermToAssign.get(t);
                if(Operators.model.keySet().contains(assign)){
                  if(!Operators.inputOrRandVar.contains(next)){//当前变量不在inputOrRandVar中
                    if(next.contains("a3")&&Operators.model.get(assign).toString().equals("0.0")){
                      int i=1;
                      i=i+1;
                    }
                     Operators.lastValues.put(next, Operators.model.get(assign).toString());
                  }
                 }
                //System.out.println(t+"="+Operators.model.get(assign));
              }

            }
          }
          else {
            String curTerms[] = curTerm.split("&&");
            for (int i = 0; i < curTerms.length; i++) {
              String subTerm = curTerms[i].trim();
              if (!subTerm.equals("true") && !subTerm.startsWith("!")) {
                successor.setTransition(null);
                break;
              }
            }
          }
          while (count != 0) {
            f.remove(f.size() - 1);
            count--;
          }
          CounterexampleTraceInfo<I> info1 = new CounterexampleTraceInfo<I>();
          return info1;
        //}
      }
      if (edgeSuc instanceof CStatementEdge) {//eg: if " int *x=malloc() ", then x!=0 ;
        CStatement s = ((CStatementEdge) edgeSuc).getStatement();
        if (s instanceof CFunctionCallAssignmentStatement) {
          CFunctionCallExpression right = ((CFunctionCallAssignmentStatement) s).getRightHandSide();
          if (right.getFunctionNameExpression().toASTString().contains("alloc")) {
            CExpression left = ((CFunctionCallAssignmentStatement) s).getLeftHandSide();
            String l = left.toASTString();
            String func = edgeSuc.getSuccessor().getFunctionName();
            l = l + "=" + "0x0001;";
            String addinfo = "int " + func + "(){" + l + "}";
            ParseResult myString;
            try {
              myString = PropositionInfo.parser.parseString(addinfo);
              Map<String, FunctionEntryNode> fn = myString.getFunctions();
              CFANode node = fn.get(func);
              while (node.getNumLeavingEdges() != 0) {
                CFAEdge e = node.getLeavingEdge(0);
                if (e.getRawStatement().equals(l)) {
                  addEdge = e;
                  break;
                }
                node = e.getSuccessor();
              }
            } catch (org.sosy_lab.cpachecker.exceptions.ParserException e1) {
              // TODO Auto-generated catch block
              e1.printStackTrace();
            }
          }
        }
      }
      if (addEdge == null && (edgeSuc.getDescription().contains("<<") || edgeSuc.getDescription().contains(">>"))) {
        String des = edgeSuc.getDescription().toString();
        List<String> list = GlobalInfo.getInstance().getMyString(edgeSuc);
        //System.out.println("list=" + list);
        for (String s : list) {
          while (des.contains(">> " + s)) {
            String tmp =
                des.substring(0, des.indexOf(">> " + s)) + des.substring(des.indexOf(">> " + s) + s.length() + 3);
            des = tmp;
          }
          while (des.contains(">> (" + s + ")")) {
            String tmp =
                des.substring(0, des.indexOf(">> (" + s + ")"))
                    + des.substring(des.indexOf(">> (" + s + ")") + s.length() + 5);
            des = tmp;
          }
          while (des.contains("<< " + s)) {
            String tmp =
                des.substring(0, des.indexOf("<< " + s)) + des.substring(des.indexOf("<< " + s) + s.length() + 3);
            des = tmp;
          }
          while (des.contains("<< (" + s + ")")) {
            String tmp =
                des.substring(0, des.indexOf("<< (" + s + ")"))
                    + des.substring(des.indexOf("<< (" + s + ")") + s.length() + 5);
            des = tmp;
          }
        }
        // des=des.replaceAll("<<"," ");
        // des=des.replaceAll(">>"," ");
        if (des.contains("=")) {

          String func = edgeSuc.getSuccessor().getFunctionName();
          // exp=exp.substring(0,exp.indexOf("="))+"=0x0001;";
          String addinfo = "int " + func + "(){" + des + "}";
          ParseResult myString;
          try {
            myString = PropositionInfo.parser.parseString(addinfo);
            Map<String, FunctionEntryNode> fn = myString.getFunctions();
            CFANode node = fn.get(func);
            while (node.getNumLeavingEdges() != 0) {
              CFAEdge e = node.getLeavingEdge(0);
              if (e.getRawStatement().equals(des)) {
                addEdge = e;
                break;
              }
              node = e.getSuccessor();
            }
          } catch (org.sosy_lab.cpachecker.exceptions.ParserException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
          }

        }
      }
      if (addEdge != null){
        // edgeSuc = addEdge;
         pFSuc = pmgr.makeAnd1(sucPPath, addEdge);
       }
       else{
         pFSuc = pmgr.makeAnd1(sucPPath, edgeSuc);
       }
//      if(edgeSuc.isKeyEdge()){//<yangkai> 是关键边时，将当前边的公式加入到之前得到的公式中
//       if (!pFSuc.getFormula().isTrue())
//         f.add(pFSuc.getFormula());
//      }
//      else{
//        pFSuc=sucPPath;
//      }
      //sucPPath=pFSuc;
      //f1 = new ArrayList<Formula>(f);
      if (fmgr.useBitwiseAxioms()) {
        addBitwiseAxioms(f);
      }

      //f = Collections.unmodifiableList(f);
      logger.log(Level.ALL, "Counterexample trace formulas:", f);

      // now f is the DAG formula which is satisfiable iff there is a
      // concrete counterexample


      // Check if refinement problem is not too big
      if (maxRefinementSize > 0) {
        int size = fmgr.dumpFormula(fmgr.makeConjunction(f)).length();
        if (size > maxRefinementSize) {
          logger.log(Level.FINEST, "Skipping refinement because input formula is", size, "bytes large.");
          throw new RefinementFailedException(Reason.TooMuchUnrolling, null);
        }
      }


      // Check feasibility of counterexample
      logger.log(Level.FINEST, "Checking feasibility of counterexample trace");
      stats.cexAnalysisSolverTimer.start();

      boolean spurious = false;
      //List<T> itpGroupsIds;
      //int spur=0;
      try {

        if (shortestTrace && getUsefulBlocks) {

          //f = Collections.unmodifiableList(getUsefulBlocks(f, useSuffix, useZigZag));
        }

        if (dumpInterpolationProblems) {
          dumpInterpolationProblem(f);
        }

        // initialize all interpolation group ids with "null"
        //itpGroupsIds = new ArrayList<T>(Collections.<T> nCopies(f.size(), null));

        /* if(b){
           if (getUsefulBlocks || !shortestTrace) {
             spurious = checkInfeasibilityOfFullTrace(f, itpGroupsIds, pFirstItpProver);

           } else {
             spurious = checkInfeasabilityOfShortestTrace(f, itpGroupsIds, pFirstItpProver);
           }
         }
         else{
           spurious=false;
         }*/

      } finally {
        stats.cexAnalysisSolverTimer.stop();
      }
      logger.log(Level.FINEST, "Counterexample trace is", (spurious ? "infeasible" : "feasible"));
      CounterexampleTraceInfo<I> info = new CounterexampleTraceInfo<I>();
      int spu = 0;
      String funcname = "";
      if (!entryMain) {
        funcname = edgeSuc.getPredecessor().getFunctionName();
        if (funcname.equals("main") && edgeSuc.getDescription().equals("Function start dummy edge")) {
          entryMain = true;
          Operators.entryMain=true;
        }
      }
      if (entryMain) {
        count = generateOneStepFormula(f, pFSuc, edgeSuc, transition, proposition);
        if (first.equals("Global") || first.equals(edgeSuc.getPredecessor().getFunctionName()))
          spu = checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
        if (spu == 1) { //f1 is false
          Operators.isUnSat=true;
          successor.setTransition(null);
        }
        else{
          Operators.isUnSat=false;
          try {
            Operators.model = pFirstItpProver.getModel();
          } catch (SolverException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
          Iterator<String> it=Operators.lastTerms.keySet().iterator();
          while(it.hasNext()){
            String next=it.next();
            Term t=Operators.lastTerms.get(next);
            AssignableTerm assign = Operators.modelTermToAssign.get(t);
            if(Operators.model.keySet().contains(assign)){
              if(!Operators.inputOrRandVar.contains(next)){//当前变量不在inputOrRandVar中
                if(next.contains("a3")&&Operators.model.get(assign).toString().equals("0.0")){
                  int i=1;
                  i=i+1;
                }
                 Operators.lastValues.put(next, Operators.model.get(assign).toString());
              }
             }
            //System.out.println(t+"="+Operators.model.get(assign));
          }
        }

        while (count != 0) {
          f.remove(f.size() - 1);
          count--;
        }
      } else {
        // String curTerm = transition.getLabel().trim();
        // String nextTerm = transition.getTarget_state();
        curTerm = curTerm.replaceAll("[\\(|\\)| ]", "");
        String curTerms[] = curTerm.split("&&");
        for (int i = 0; i < curTerms.length; i++) {
          String subTerm = curTerms[i].trim();
          if (!subTerm.equals("true") && !subTerm.startsWith("!")) {
            successor.setTransition(null);
            break;
          }
        }
      }
      return info;
    } finally {
      pFirstItpProver.reset();
      stats.cexAnalysisTimer.stop();
    }
  }

  /**
   * Counterexample analysis and predicate discovery.
   * @param pFormulas the formulas for the path
   * @param elementsOnPath the ARGElements on the path (may be empty if no branching information is required)
   * @param pItpProver interpolation solver used
   * @return counterexample info with predicated information
   * @throws CPAException
   */
  private <T> CounterexampleTraceInfo<I> buildCounterexampleTraceWithSpecifiedItp(
      List<Formula> pFormulas, Set<ARGState> elementsOnPath, InterpolatingTheoremProver<T> pItpProver)
      throws CPAException, InterruptedException {

    logger.log(Level.FINEST, "Building counterexample trace");
    /*for(Formula f1:pFormulas){
      //System.out.println("f11=>"+f1);
    }*/
    stats.cexAnalysisTimer.start();
    pItpProver.init();
    try {

      // Final adjustments to the list of formulas
      List<Formula> f = new ArrayList<Formula>(pFormulas); // copy because we will change the list

      if (fmgr.useBitwiseAxioms()) {
        addBitwiseAxioms(f);
      }

      f = Collections.unmodifiableList(f);
      logger.log(Level.ALL, "Counterexample trace formulas:", f);



      // now f is the DAG formula which is satisfiable iff there is a
      // concrete counterexample


      // Check if refinement problem is not too big
      if (maxRefinementSize > 0) {
        int size = fmgr.dumpFormula(fmgr.makeConjunction(f)).length();
        if (size > maxRefinementSize) {
          logger.log(Level.FINEST, "Skipping refinement because input formula is", size, "bytes large.");
          throw new RefinementFailedException(Reason.TooMuchUnrolling, null);
        }
      }


      // Check feasibility of counterexample
      logger.log(Level.FINEST, "Checking feasibility of counterexample trace");
      stats.cexAnalysisSolverTimer.start();

      boolean spurious;
      List<T> itpGroupsIds;
      try {
        if (shortestTrace && getUsefulBlocks) {
          f = Collections.unmodifiableList(getUsefulBlocks(f, useSuffix, useZigZag));
        }
        if (dumpInterpolationProblems) {
          dumpInterpolationProblem(f);
        }
        // initialize all interpolation group ids with "null"
        itpGroupsIds = new ArrayList<T>(Collections.<T> nCopies(f.size(), null));
        //System.out.println("itpGroupsIds=>"+itpGroupsIds);
        if (getUsefulBlocks || !shortestTrace) {
          spurious = checkInfeasibilityOfFullTrace(f, itpGroupsIds, pItpProver);

        } else {
          spurious = checkInfeasabilityOfShortestTrace(f, itpGroupsIds, pItpProver);
        }
        assert itpGroupsIds.size() == f.size();
        assert !itpGroupsIds.contains(null); // has to be filled completely
//        if(!spurious){//<yangkai> 找到一条反例时，记录求解器给出的变量的值
//          Operators.valuesOfkeyVars = pItpProver.getModel().toString();
//        }
      } finally {
        stats.cexAnalysisSolverTimer.stop();
      }
      logger.log(Level.FINEST, "Counterexample trace is", (spurious ? "infeasible" : "feasible"));
      // Get either interpolants or error path information
      CounterexampleTraceInfo<I> info;
      if (spurious) {
        List<Formula> interpolants = getInterpolants(pItpProver, itpGroupsIds);
        ////System.out.println(interpolants);
        if (verifyInterpolants) {
          verifyInterpolants(interpolants, f, pItpProver);
        }
        info = extractPredicates(interpolants);
      } else {
        // this is a real bug
        info = getErrorPath(f, pItpProver, elementsOnPath);
      }
      logger.log(Level.ALL, "Counterexample information:", info);
      return info;
    } finally {
      pItpProver.reset();
      stats.cexAnalysisTimer.stop();
    }
  }
  private <T> CounterexampleTraceInfo<I> buildCounterexampleTraceWithSpecifiedItpForArray(List<Formula> f,
      ARGState successor,
      CFANode loc, InterpolatingTheoremProver<T> pFirstItpProver, Proposition proposition, boolean b)
      throws InterruptedException, RefinementFailedException, CPATransferException {


    logger.log(Level.FINEST, "Building counterexample trace");
    stats.cexAnalysisTimer.start();
    pFirstItpProver.init();
    try {
      // Final adjustments to the list of formulas
      //List<Formula> f = pSuccessor.getFirst().getFormulas(); // copy because we will change the list
      ARGState sucParent = successor.getParents().iterator().next();

      CFAEdge edgeSuc = sucParent.getEdgeToChild(successor);
      CFAEdge edgeSummary = null;
      if (edgeSuc instanceof CFunctionCallEdge) {
        edgeSummary = ((CFunctionCallEdge) edgeSuc).getSummaryEdge();
        /*          FunctionSummaryEdge summary=AbstractStates.extractLocation(sucParent).getLeavingSummaryEdge();
                  if(summary!=null)
                    edgeSuc=summary;*/
      }
      //if(edgeSuc!=null){
      PathFormula sucPPath = sucParent.getPathFormula();
      PathFormula pFSuc = pmgr.makeAnd1(sucPPath, edgeSuc);
      f.add(pFSuc.getFormula());
      // }
      if (fmgr.useBitwiseAxioms()) {
        addBitwiseAxioms(f);
      }

      //f = Collections.unmodifiableList(f);
      logger.log(Level.ALL, "Counterexample trace formulas:", f);

      // now f is the DAG formula which is satisfiable iff there is a
      // concrete counterexample


      // Check if refinement problem is not too big
      if (maxRefinementSize > 0) {
        int size = fmgr.dumpFormula(fmgr.makeConjunction(f)).length();
        if (size > maxRefinementSize) {
          logger.log(Level.FINEST, "Skipping refinement because input formula is", size, "bytes large.");
          throw new RefinementFailedException(Reason.TooMuchUnrolling, null);
        }
      }


      // Check feasibility of counterexample
      logger.log(Level.FINEST, "Checking feasibility of counterexample trace");
      stats.cexAnalysisSolverTimer.start();

      boolean spurious;
      List<T> itpGroupsIds;
      Proposition p = new Proposition();
      //int spur=0;
      try {

        if (shortestTrace && getUsefulBlocks) {

          //f = Collections.unmodifiableList(getUsefulBlocks(f, useSuffix, useZigZag));
        }

        if (dumpInterpolationProblems) {
          dumpInterpolationProblem(f);
        }

        // initialize all interpolation group ids with "null"
        itpGroupsIds = new ArrayList<T>(Collections.<T> nCopies(f.size(), null));

        if (b) {//b是isTwo================注意：spurious==1表示这条路径是假的，不可达======spurious==0表示这条路径是真的，可达

          if (getUsefulBlocks || !shortestTrace) {
            spurious = checkInfeasibilityOfFullTrace(f, itpGroupsIds, pFirstItpProver);

          } else {
            spurious = checkInfeasabilityOfShortestTrace(f, itpGroupsIds, pFirstItpProver);
          }
        }
        else {
          spurious = false;
        }

      } finally {
        stats.cexAnalysisSolverTimer.stop();
      }
      //spurious=spur==1?true:false;
      logger.log(Level.FINEST, "Counterexample trace is", (spurious ? "infeasible" : "feasible"));
      //itpGroupsIds = new ArrayList<T>(Collections.<T>nCopies(f.size(), null));
      ////System.out.println("itpGroupsIds=>"+itpGroupsIds);
      CounterexampleTraceInfo<I> info = new CounterexampleTraceInfo<I>();
      //if(b&&spurious){
      // List<Formula> interpolants = getInterpolants1(pFirstItpProver, itpGroupsIds);
      // info = extractPredicates(interpolants);
      //  info.setInterpolants(interpolants);

      //}
      info.setSpurious(spurious);
      //计算successor所满足的命题,即对于一个命题p,是满足p还是满足!p============================================================判断是p还是！p
      // if(edgeSummary!=null)
      //f.remove(f.size()-1);
      List<String> func = new ArrayList<String>(1);
      Map<Pair<String, String>, String> sucPro = new HashMap<Pair<String, String>, String>();//空的===={}======
      // Map<Pair<String,String>,String> sucPro1=new HashMap<Pair<String,String>,String>();//空的===={}======
      //Map<Pair<String,String>,> sucPro=new HashMap<>();

      //加入自己的公式===================================================================================================addMyFormula方法
      //result如果没有遇到，会返回空，遇到则会返回相应的结果{(!d, !(a<length))=(not (< 3.0 4.0))}
      Map<Integer, Map<Pair<String, String>, PathFormula>> results =
          addMyFormulaForArray(successor, loc, proposition, sucPro, func);//会有sucPro改变，如果是没用到的，会返回！r和！d   即{(!r, !(a==a))=main, (!d, !(a<length))=main}
      Map<Pair<String, String>, String> sucPro1 = new HashMap<Pair<String, String>, String>(sucPro);
      for (Map.Entry<Integer, Map<Pair<String, String>, PathFormula>> entry : results.entrySet()) {
        Map<Pair<String, String>, PathFormula> result = entry.getValue();
        Iterator<Pair<String, String>> iterator = result.keySet().iterator();
        //List<Pair<String,String>> wait=new ArrayList<Pair<String,String>>();


        while (iterator.hasNext()) {
          pFirstItpProver.reset();
          pFirstItpProver.init();
          Pair<String, String> pair = iterator.next();
          String first = pair.getFirst();
          String second = pair.getSecond();
          Formula formula = null;
          PathFormula pathFormula = result.get(pair);
          //int t = checkInfeasibilityOfFullTrace1(f,pFirstItpProver);

          if (pathFormula != null)
            formula = pathFormula.getFormula();

          //龙测试


          for (Formula ff : f) {
            ((SmtInterpolFormula) ff).getTerm().getTheory();

          }


          //龙测试完毕
          if (formula != null)
            f.add(formula);


          itpGroupsIds = new ArrayList<T>(Collections.<T> nCopies(f.size(), null));


          //判断加入边后的真假===========================================================================================加入边的真假
          int spur = checkInfeasibilityOfFullTrace1(f, pFirstItpProver);
          //System.out.println("my->result->"+spur);
          f.remove(formula);
          if (spur == 1) {//是假的，！d是假的，
            if (!spurious) {//当前节点不可达
              if (first.startsWith("!")) {
                first = first.substring(1);
                second = second.substring(2, second.length() - 1);
              }
              else {
                first = "!" + first;
                second = "!(" + second + ")";
              }
              sucPro.put(Pair.of(first, second), proposition.getPropositions().get(pair));
            }
            else {
              continue;
            }
          }
          else if (spur == 0) {
            System.out.println("=========================================是越界边======================" + result);
            sucPro1.put(pair, proposition.getPropositions().get(pair));
            break;

          }
          else {
            Iterator<Pair<String, String>> ppt = successor.getProposition().getPropositions().keySet().iterator();
            while (ppt.hasNext()) {
              Pair<String, String> ps = ppt.next();
              if (first.contains(ps.getFirst())) {
                sucPro.put(ps, proposition.getPropositions().get(pair));
                break;
              }
            }
          }
        }

      }
      /*Iterator<Pair<String,String>> itp=sucPro.keySet().iterator();
      Map<Pair<String,String>,String> tmpMap=new HashMap<>();
      while(itp.hasNext()&&wait.size()!=0){
        Pair<String,String> pair=itp.next();
        String first=pair.getFirst();
        String tmp=first.replaceAll("1","2");
        for(int i=0;i<wait.size();++i){
          Pair<String,String> wp=wait.get(i);
          String wf=wp.getFirst();
          String ws=wp.getSecond();
          if(wf.equals("!"+tmp)||wf.equals(tmp)||tmp.equals("!"+wf)){
            if(!wf.startsWith("!")&&first.startsWith("!")){
              wf="!"+wf;
              ws="!("+ws+")";

            }
            else if(wf.startsWith("!")&&!first.startsWith("!")){
              wf=wf.substring(1);
              ws=ws.substring(2,ws.length()-1);
            }
            tmpMap.put(Pair.of(wf,ws),proposition.getPropositions().get(pair));
            wait.remove(pair);
            break;
          }
        }
      }
      sucPro.putAll(tmpMap);
      tmpMap.clear();*/
      if (sucPro1.size() == 1) {
        p.setPropositions(sucPro);
      } else {
        p.setPropositions(sucPro1);
      }
      info.setProposition(p);
      return info;
    } finally {
      pFirstItpProver.reset();
      stats.cexAnalysisTimer.stop();
    }

  }

  //很重要的一个方法==============================================================================================判断是否是r还是!r
  private boolean onRight(String s, String var) {//判断声明语句中,*x或x->是否出现在等号右边
    // TODO Auto-generated method stub
    if (!s.contains("="))
      return false;
    s = s.substring(s.indexOf("=") + 1);
    if (s.contains("*" + var) || s.contains(var + "->"))
      return true;
    return false;
  }


  //很重要的一个方法=================================================================加入自己的边判断，具体方法addMyFormula======里面有判断是否是r与!r
  /*
   * 把命题对应的CFAEdge转化为PathFormula
   */
  private Map<Pair<String, String>, PathFormula> addMyFormulaForPointer(ARGState successor, PathFormula pFSuc,
      Proposition proposition, Map<Pair<String, String>, String> sucPro, List<String> func, CFAEdge edgeSummary,
      CFAEdge edgeSuc) throws CPATransferException {
    // TODO Auto-generated method stub
    PathFormula sucPathFormula = pFSuc;
    Map<Pair<String, String>, PathFormula> result = new HashMap<Pair<String, String>, PathFormula>();
    Map<Pair<String, String>, CFAEdge> resultMap = new HashMap<Pair<String, String>, CFAEdge>();
    Map<Pair<String, String>, String> pm = proposition.negative().getPropositions();
    Map<Pair<String, String>, CFAEdge> pe = proposition.getPropEdges();//命题对应的CFAEdge
    Iterator<Pair<String, String>> iterator = pm.keySet().iterator();
    //ARGState sucParent=successor.getParents().iterator().next();//这里suc只有一个parent
    CFAEdge edge = edgeSummary != null ? edgeSummary : edgeSuc;
    String function = edge.getPredecessor().getFunctionName();
    func.add(function);

    while (iterator.hasNext()) {
      Pair<String, String> pair = iterator.next();
      if (function.equals(pm.get(pair)) || pm.get(pair).equals("Global")) {
        resultMap.put(pair, pe.get(pair));
      }
      else {
        sucPro.put(pair, pm.get(pair));
      }
    }
    Iterator<Pair<String, String>> it = resultMap.keySet().iterator();
    while (it.hasNext()) {
      Pair<String, String> next = it.next();

      if (!pe.keySet().contains(next)) {//这是一个c语言无法描述的命题,表示使用了*x或x->
        String first = next.getFirst();
        String second = next.getSecond();
        if (first.startsWith("!")) {
          first = first.substring(1);
          second = second.substring(2, second.length() - 1);
        }
        //System.out.println("second="+second);
        var = second.substring(0, second.indexOf("==")).trim();
        //System.out.println("var="+var);

        String description = edge.getDescription().replaceAll("\n", " ");
        //System.out.println("description="+description);
        boolean myjudge = CFAUtils.judge(edge, var);
        if (!myjudge) {
          first = "!" + first;
          second = "!(" + second + ")";
        }
        Pair<String, String> pair = Pair.of(first, second);
        sucPro.put(pair, proposition.getPropositions().get(pair));
        continue;
      }
      //System.out.println("next="+next);
      CFAEdge e = resultMap.get(next);
      e.setPredecessor(edge.getPredecessor());
      e.setSuccessor(edge.getSuccessor());
      //e.setSuccessor(sucNode.getNumLeavingEdges()!=0?sucNode.getLeavingEdge(0).getSuccessor():sucNode);
      PathFormula p = pmgr.makeAnd1(sucPathFormula, e);
      result.put(next, p);
    }
    ////System.out.println("sucFormula=>"+sucPathFormula);
    return result;
  }

  /*
   * 把命题对应的CFAEdge转化为PathFormula
   */
  private Map<Pair<String, String>, PathFormula> addMyFormulaForSimpleProperty(ARGState successor, PathFormula pFSuc,
      Proposition proposition, Map<Pair<String, String>, String> sucPro, List<String> func, CFAEdge edgeSummary,
      CFAEdge edgeSuc) throws CPATransferException {
    // TODO Auto-generated method stub
    PathFormula sucPathFormula = pFSuc;
    Map<Pair<String, String>, PathFormula> result = new HashMap<Pair<String, String>, PathFormula>();
    Map<Pair<String, String>, CFAEdge> resultMap = new HashMap<Pair<String, String>, CFAEdge>();
    Map<Pair<String, String>, String> pm = proposition.negative().getPropositions();
    Map<Pair<String, String>, CFAEdge> pe = proposition.getPropEdges();//命题对应的CFAEdge
    Iterator<Pair<String, String>> iterator = pm.keySet().iterator();
    //ARGState sucParent=successor.getParents().iterator().next();//这里suc只有一个parent
    CFAEdge edge = edgeSummary != null ? edgeSummary : edgeSuc;
    String function = edge.getPredecessor().getFunctionName();
    func.add(function);

    while (iterator.hasNext()) {
      Pair<String, String> pair = iterator.next();
      if (function.equals(pm.get(pair)) || pm.get(pair).equals("Global")) {
        resultMap.put(pair, pe.get(pair));
      }
      else {
        sucPro.put(pair, pm.get(pair));
      }
    }
    Iterator<Pair<String, String>> it = resultMap.keySet().iterator();
    while (it.hasNext()) {
      Pair<String, String> next = it.next();
      //System.out.println("next="+next);
      CFAEdge e = resultMap.get(next);
      e.setPredecessor(edge.getPredecessor());
      e.setSuccessor(edge.getSuccessor());
      //e.setSuccessor(sucNode.getNumLeavingEdges()!=0?sucNode.getLeavingEdge(0).getSuccessor():sucNode);
      PathFormula p = pmgr.makeAnd1(sucPathFormula, e);
      result.put(next, p);
    }
    ////System.out.println("sucFormula=>"+sucPathFormula);
    return result;
  }

  /*
   * 把命题对应的CFAEdge转化为PathFormula
   */
  private Map<Integer, Map<Pair<String, String>, PathFormula>> addMyFormulaForArray(ARGState successor,
      CFANode sucNode, Proposition proposition, Map<Pair<String, String>, String> sucPro, List<String> func)
      throws CPATransferException {
    // TODO Auto-generated method stub
    PathFormula sucPathFormula = successor.getPathFormula();
    //Formula sucFormula=sucPathFormula.getFormula();
    ////System.out.println("sucFormula=>"+sucPathFormula);
    Map<Pair<String, String>, PathFormula> result = new HashMap<Pair<String, String>, PathFormula>();//此处是true
    Map<Integer, Map<Pair<String, String>, PathFormula>> results =
        new HashMap<Integer, Map<Pair<String, String>, PathFormula>>();
    Map<Pair<String, String>, CFAEdge> resultMap = new HashMap<Pair<String, String>, CFAEdge>();

    Map<Pair<String, String>, String> pm = proposition.negative().getPropositions();//取出proposition中的！的，(!r, !(p==p))=main, (!d, !(p!=0))=main
    Map<Pair<String, String>, CFAEdge> pe = proposition.getPropEdges();//命题对应的CFAEdge，取出边：{(d, p!=0)=Line 1:  N26 -{[p != 0]}-> N28, (!d, !(p!=0))=Line 1:  N41 -{[!(p != 0)]}-> N43}

    Iterator<Pair<String, String>> iterator = pm.keySet().iterator();//对(!r, !(p==p))与(!d, !(p!=0))进行遍历

    ARGState sucParent = successor.getParents().iterator().next();//这里suc只有一个parent
    //得到边，succesor的对应边edge：Line 0:  N1 -{INIT GLOBAL VARS}-> N22
    CFAEdge edge =
        AbstractStates.extractLocation(sucParent).getLeavingSummaryEdge() != null ? AbstractStates.extractLocation(
            sucParent).getLeavingSummaryEdge() : sucParent.getEdgeToChild(successor);
    String function = edge.getSuccessor().getFunctionName();//得到function的名字：此处是main
    func.add(function);//原来为空，加入上面的main  现在是main

    while (iterator.hasNext()) {
      Pair<String, String> pair = iterator.next();
      if (function.equals(pm.get(pair)) || pm.get(pair).equals("Global")) {//如果是r则resultMap中的edge为空null，因为pe.get(pair)没有对应的
        //resultMap结果：{(!r, !(p==p))=null, (!d, !(p!=0))=Line 1:  N41 -{[!(p != 0)]}-> N43}
        resultMap.put(pair, pe.get(pair));
      }
      else {
        sucPro.put(pair, pm.get(pair));
      }
    }



    if (!(resultMap.isEmpty())) {
      Set<Pair<String, String>> its = resultMap.keySet();//取出(!r, !(p==p))与(!d, !(p!=0))遍历
      boolean myjudge = false;
      Pair<String, String> myFirstNotR = null;
      Pair<String, String> mySeconNotD = null;
      for (Pair<String, String> it : its) {//next是(!r, !(p==p))第一次==============第二次是(!d, !(p!=0))
        String myFirst = it.getFirst();
        if (myFirst.equals("!au")) {
          myFirstNotR = it;
        } else {
          mySeconNotD = it;
        }
      }

      //这是一个c语言无法描述的命题,表示使用了*x或x->===//pe中没有包括，其实pe的keySet中只有d与！d（带边的）===第一次进=============判断是r还是!r====1
      //第一部分，判断r是否满足
      if (myFirstNotR != null) {
        if (!pe.keySet().contains(myFirstNotR)) {
          String first = myFirstNotR.getFirst();//!r
          String second = myFirstNotR.getSecond();//!(p==p)
          if (first.startsWith("!")) {
            first = first.substring(1);
            second = second.substring(2, second.length() - 1);//如果是!r则变成r===============================对r进行判断，而不是!r
          }
          //System.out.println("second="+second);
          String var = second.substring(0, second.indexOf("==")).trim();//取出相应指针（变量）===p
          //System.out.println("var="+var);

          String description = edge.getDescription().replaceAll("\n", " ");//得到边描述信息：INIT GLOBAL VARS
          //System.out.println("description="+description);
          //具体判断真假========================================具体判断边上是否有r里面的指针变量==========2
          myjudge = CFAUtils.long_judge(edge, var);//没有用到指针p，返回false

          if (!myjudge) {//由于没有碰到指针或数组，还变成!r
            first = "!" + first;//变成      !r
            second = "!(" + second + ")";//变成         !(p==p)
          }
          Pair<String, String> pair = Pair.of(first, second);
          sucPro.put(pair, proposition.getPropositions().get(pair));//为true时加入{(r, a==a)=main}
        }

      }


      //System.out.println("next="+next);
      CFAEdge e = resultMap.get(mySeconNotD);

      //用到数组变量===================对边操作=============  龙开始
      if (myjudge)
      {
        try {
          List<Proposition> mypros = ArrayCheckAlgorithm.run2(proposition, edge);
          CFAUtils.subTwoLens.clear();
          int i = 0;
          PathFormula p = null;

          for (Proposition mypro : mypros) {
            Map<Pair<String, String>, PathFormula> myresult = new HashMap<Pair<String, String>, PathFormula>();
            for (Pair<String, String> mypai : mypro.getPropEdges().keySet()) {
              if (i == 0) {
                p = sucPathFormula;
              }
              if (mypai.getFirst().trim().equals("!al")) {
                e = mypro.getPropEdges().get(mypai);


                if (e != null) {
                  e.setPredecessor(edge.getPredecessor());
                  e.setSuccessor(edge.getSuccessor());
                  //e.setSuccessor(sucNode.getNumLeavingEdges()!=0?sucNode.getLeavingEdge(0).getSuccessor():sucNode);
                  if (p != null)
                    p = pmgr.makeAnd1(p, e);//sucPathFormula是true，而得到的p是(not (< 6.0 4.0))
                  myresult.put(mySeconNotD, p);
                  results.put(i, myresult);
                  p = sucPathFormula;
                }
              }
              // next=mypai;
              i++;
            }
          }
        } catch (ParserException e1) {
          // TODO Auto-generated catch block
          e1.printStackTrace();
        }

      } else {

        sucPro.put(mySeconNotD, proposition.getPropositions().get(mySeconNotD));//为true时加入{(r, a==a)=main}

      }
      //结束生成边操作=========================================龙结束








    }
    ////System.out.println("sucFormula=>"+sucPathFormula);
    return results;
  }

  /**
   * Add axioms about bitwise operations to a list of formulas, if such operations
   * are used. This is probably not that helpful currently, we would have to the
   * tell the solver that these are axioms.
   *
   * The axioms are added to the last part of the list of formulas.
   *
   * @param f The list of formulas to scan for bitwise operations.
   */
  private void addBitwiseAxioms(List<Formula> f) {
    Formula bitwiseAxioms = fmgr.makeTrue();

    for (Formula fm : f) {
      Formula a = fmgr.getBitwiseAxioms(fm);
      if (!a.isTrue()) {
        bitwiseAxioms = fmgr.makeAnd(bitwiseAxioms, a);
      }
    }

    if (!bitwiseAxioms.isTrue()) {
      logger.log(Level.ALL, "DEBUG_3", "ADDING BITWISE AXIOMS TO THE",
          "LAST GROUP: ", bitwiseAxioms);
      int lastIndex = f.size() - 1;
      f.set(lastIndex, fmgr.makeAnd(f.get(lastIndex), bitwiseAxioms));
    }
  }

  /**
   * Try to find out which formulas out of a list of formulas are relevant for
   * making the conjunction unsatisfiable.
   *
   * @param f The list of formulas to check.
   * @param suffixTrace Whether to start from the end of the list.
   * @param zigZag Whether to use a zig-zag way, using formulas from the beginning and the end.
   * @return A sublist of f that contains the useful formulas.
   */
  private List<Formula> getUsefulBlocks(List<Formula> f, boolean suffixTrace, boolean zigZag) {

    stats.cexAnalysisGetUsefulBlocksTimer.start();

    // try to find a minimal-unsatisfiable-core of the trace (as Blast does)

    TheoremProver thmProver = solver.getTheoremProver();
    thmProver.init();

    logger.log(Level.ALL, "DEBUG_1", "Calling getUsefulBlocks on path",
        "of length:", f.size());

    Formula[] needed = new Formula[f.size()];
    for (int i = 0; i < needed.length; ++i) {
      needed[i] = fmgr.makeTrue();
    }
    int pos = suffixTrace ? f.size() - 1 : 0;
    int incr = suffixTrace ? -1 : 1;
    int toPop = 0;

    while (true) {
      boolean consistent = true;
      // 1. assert all the needed constraints
      for (int i = 0; i < needed.length; ++i) {
        if (!needed[i].isTrue()) {
          thmProver.push(needed[i]);
          ++toPop;
        }
      }
      // 2. if needed is inconsistent, then return it
      if (thmProver.isUnsat()) {
        f = Arrays.asList(needed);
        break;
      }
      // 3. otherwise, assert one block at a time, until we get an
      // inconsistency
      if (zigZag) {
        int s = 0;
        int e = f.size() - 1;
        boolean fromStart = false;
        while (true) {
          int i = fromStart ? s : e;
          if (fromStart) {
            ++s;
          } else {
            --e;
          }
          fromStart = !fromStart;

          Formula t = f.get(i);
          thmProver.push(t);
          ++toPop;
          if (thmProver.isUnsat()) {
            // add this block to the needed ones, and repeat
            needed[i] = t;
            logger.log(Level.ALL, "DEBUG_1",
                "Found needed block: ", i, ", term: ", t);
            // pop all
            while (toPop > 0) {
              --toPop;
              thmProver.pop();
            }
            // and go to the next iteration of the while loop
            consistent = false;
            break;
          }

          if (e < s) {
            break;
          }
        }
      } else {
        for (int i = pos; suffixTrace ? i >= 0 : i < f.size(); i += incr) {
          Formula t = f.get(i);
          thmProver.push(t);
          ++toPop;
          if (thmProver.isUnsat()) {
            // add this block to the needed ones, and repeat
            needed[i] = t;
            logger.log(Level.ALL, "DEBUG_1",
                "Found needed block: ", i, ", term: ", t);
            // pop all
            while (toPop > 0) {
              --toPop;
              thmProver.pop();
            }
            // and go to the next iteration of the while loop
            consistent = false;
            break;
          }
        }
      }
      if (consistent) {
        // if we get here, the trace is consistent:
        // this is a real counterexample!
        break;
      }
    }

    while (toPop > 0) {
      --toPop;
      thmProver.pop();
    }

    thmProver.reset();

    logger.log(Level.ALL, "DEBUG_1", "Done getUsefulBlocks");

    stats.cexAnalysisGetUsefulBlocksTimer.stop();

    return f;
  }


  /**
   * Check the satisfiability of all formulas in a list.
   *
   * @param f The list of formulas to check.
   * @param itpGroupsIds The list where to store the references to the interpolation groups.
   * @param pItpProver The solver to use.
   * @return True if the formulas are unsatisfiable.
   * @throws InterruptedException
   */
  private <T> boolean checkInfeasibilityOfFullTrace(List<Formula> f,
      List<T> itpGroupsIds, InterpolatingTheoremProver<T> pItpProver)
      throws InterruptedException {
    // check all formulas in f at once

    for (int i = useSuffix ? f.size() - 1 : 0; useSuffix ? i >= 0 : i < f.size(); i += useSuffix ? -1 : 1) {
      ////System.out.println(i+":=>"+f.get(i));
      itpGroupsIds.set(i, pItpProver.addFormula(f.get(i)));
    }
    boolean bool = pItpProver.isUnsat();
    // //System.out.println("bool=>"+bool);
    return bool;
  }

  private <T> int checkInfeasibilityOfFullTrace1(List<Formula> f, InterpolatingTheoremProver<T> pItpProver)
      throws InterruptedException {
    // check all formulas in f at once

    for (int i = useSuffix ? f.size() - 1 : 0; useSuffix ? i >= 0 : i < f.size(); i += useSuffix ? -1 : 1) {
      ////System.out.println(i+":=>"+f.get(i));
      pItpProver.addFormula(f.get(i));
    }
    int result = pItpProver.isUnsat1();
    return result;
  }

  /**
   * Check the satisfiability of a list of formulas, while trying to use as few
   * formulas as possible to make it unsatisfiable.
   *
   * @param traceFormulas The list of formulas to check.
   * @param itpGroupsIds The list where to store the references to the interpolation groups.
   * @param pItpProver The solver to use.
   * @return True if the formulas are unsatisfiable.
   * @throws InterruptedException
   */
  private <T> boolean checkInfeasabilityOfShortestTrace(List<Formula> traceFormulas,
      List<T> itpGroupsIds, InterpolatingTheoremProver<T> pItpProver) throws InterruptedException {
    Boolean tmpSpurious = null;

    if (useZigZag) {
      int e = traceFormulas.size() - 1;
      int s = 0;
      boolean fromStart = false;
      while (s <= e) {
        int i = fromStart ? s : e;
        if (fromStart) {
          s++;
        } else {
          e--;
        }
        fromStart = !fromStart;

        tmpSpurious = null;
        Formula fm = traceFormulas.get(i);
        itpGroupsIds.set(i, pItpProver.addFormula(fm));
        if (!fm.isTrue()) {
          if (pItpProver.isUnsat()) {
            tmpSpurious = Boolean.TRUE;
            for (int j = s; j <= e; ++j) {
              itpGroupsIds.set(j, pItpProver.addFormula(traceFormulas.get(j)));
            }
            break;
          } else {
            tmpSpurious = Boolean.FALSE;
          }
        }
      }

    } else {
      for (int i = useSuffix ? traceFormulas.size() - 1 : 0; useSuffix ? i >= 0 : i < traceFormulas.size(); i +=
          useSuffix ? -1 : 1) {

        tmpSpurious = null;
        Formula fm = traceFormulas.get(i);
        itpGroupsIds.set(i, pItpProver.addFormula(fm));
        if (!fm.isTrue()) {
          if (pItpProver.isUnsat()) {
            tmpSpurious = Boolean.TRUE;
            // we need to add the other formulas to the itpProver
            // anyway, so it can setup its internal state properly
            for (int j = i + (useSuffix ? -1 : 1); useSuffix ? j >= 0 : j < traceFormulas.size(); j +=
                useSuffix ? -1 : 1) {
              itpGroupsIds.set(j, pItpProver.addFormula(traceFormulas.get(j)));
            }
            break;
          } else {
            tmpSpurious = Boolean.FALSE;
          }
        }
      }
    }

    return (tmpSpurious == null) ? pItpProver.isUnsat() : tmpSpurious;
  }

  /**
   * Get the interpolants from the solver after the formulas have been proved
   * to be unsatisfiable.
   *
   * @param pItpProver The solver.
   * @param itpGroupsIds The references to the interpolation groups
   * @return A list of all the interpolants.
   */
  private <T> List<Formula> getInterpolants(
      InterpolatingTheoremProver<T> pItpProver, List<T> itpGroupsIds) {

    List<Formula> interpolants = Lists.newArrayListWithExpectedSize(itpGroupsIds.size() - 1);

    // The counterexample is spurious. Get the interpolants.

    // how to partition the trace into (A, B) depends on whether
    // there are function calls involved or not: in general, A
    // is the trace from the entry point of the current function
    // to the current point, and B is everything else. To implement
    // this, we keep track of which function we are currently in.
    // if we don't want "well-scoped" predicates, A always starts at the beginning
    Deque<Integer> entryPoints = null;
    if (wellScopedPredicates) {
      entryPoints = new ArrayDeque<Integer>();
      entryPoints.push(0);
    }

    // //System.out.println("interpolants----------");//求插值，加插值公式
    //System.out.println("pItpProver"+pItpProver.getClass().toString());
    for (int i = 0; i < itpGroupsIds.size() - 1; ++i) {
      // last iteration is left out because B would be empty
      ////System.out.println("itpIds=>"+itpGroupsIds.get(i));
      final int start_of_a = (wellScopedPredicates ? entryPoints.peek() : 0);
      logger.log(Level.ALL, "Looking for interpolant for formulas from",
          start_of_a, "to", i);
      if(i==1225)
        i=i+1-1;
      stats.cexAnalysisSolverTimer.start();
      Formula itp = pItpProver.getInterpolant(itpGroupsIds.subList(start_of_a, i + 1));
      stats.cexAnalysisSolverTimer.stop();
      if(itp.toString().contains("::")){
        SSAMapInfo.predicates+=itp.toString();
      }

      if (dumpInterpolationProblems) {
        File dumpFile = formatFormulaOutputFile("interpolant", i);
        fmgr.dumpFormulaToFile(itp, dumpFile);
      }
      ////System.out.println(itp);
      interpolants.add(itp);

      // TODO wellScopedPredicates have been disabled

      // TODO the following code relies on the fact that there is always an abstraction on function call and return

      // If we are entering or exiting a function, update the stack
      // of entry points
      // TODO checking if the abstraction node is a new function
      //        if (wellScopedPredicates && e.getAbstractionLocation() instanceof FunctionEntryNode) {
      //          entryPoints.push(i);
      //        }
      // TODO check we are returning from a function
      //        if (wellScopedPredicates && e.getAbstractionLocation().getEnteringSummaryEdge() != null) {
      //          entryPoints.pop();
      //        }
    }

    return interpolants;
  }

  private <T> void verifyInterpolants(List<Formula> interpolants, List<Formula> formulas,
      InterpolatingTheoremProver<T> prover) throws SolverException, InterruptedException {
    stats.interpolantVerificationTimer.start();
    try {

      final int n = interpolants.size();
      assert n == (formulas.size() - 1);

      // The following three properties need to be checked:
      // (A)                          true      & f_0 => itp_0
      // (B) \forall i \in [1..n-1] : itp_{i-1} & f_i => itp_i
      // (C)                          itp_{n-1} & f_n => false

      // Check (A)
      if (!checkImplication(formulas.get(0), interpolants.get(0), prover)) { throw new SolverException(
          "First interpolant is not implied by first formula"); }

      // Check (B).
      for (int i = 1; i <= (n - 1); i++) {
        Formula conjunct = fmgr.makeAnd(interpolants.get(i - 1), formulas.get(i));

        if (!checkImplication(conjunct, interpolants.get(i), prover)) { throw new SolverException("Interpolant "
            + interpolants.get(i) + " is not implied by previous part of the path"); }
      }

      // Check (C).
      Formula conjunct = fmgr.makeAnd(interpolants.get(n - 1), formulas.get(n));
      if (!checkImplication(conjunct, fmgr.makeFalse(), prover)) { throw new SolverException(
          "Last interpolant fails to prove infeasibility of the path"); }


      // Furthermore, check if the interpolants contains only the allowed variables
      List<Set<String>> variablesInFormulas = Lists.newArrayListWithExpectedSize(formulas.size());
      for (Formula f : formulas) {
        variablesInFormulas.add(fmgr.extractVariables(f));
      }

      for (int i = 0; i < interpolants.size(); i++) {

        Set<String> variablesInA = new HashSet<String>();
        for (int j = 0; j <= i; j++) {
          // formula i is in group A
          variablesInA.addAll(variablesInFormulas.get(j));
        }

        Set<String> variablesInB = new HashSet<String>();
        for (int j = i + 1; j < formulas.size(); j++) {
          // formula i is in group A
          variablesInB.addAll(variablesInFormulas.get(j));
        }

        Set<String> allowedVariables = Sets.intersection(variablesInA, variablesInB).immutableCopy();
        Set<String> variablesInInterpolant = fmgr.extractVariables(interpolants.get(i));

        variablesInInterpolant.removeAll(allowedVariables);

        if (!variablesInInterpolant.isEmpty()) { throw new SolverException("Interpolant " + interpolants.get(i)
            + " contains forbidden variable(s) " + variablesInInterpolant); }
      }

    } finally {
      stats.interpolantVerificationTimer.stop();
    }
  }

  private <T> boolean checkImplication(Formula a, Formula b, InterpolatingTheoremProver<T> prover)
      throws InterruptedException {
    // check unsatisfiability of negation of (a => b),
    // i.e., check unsatisfiability of (a & !b)
    Formula f = fmgr.makeAnd(a, fmgr.makeNot(b));
    prover.reset();
    prover.init();

    prover.addFormula(f);
    boolean unsat = prover.isUnsat();
    return unsat;
  }

  /**
   * Get the predicates out of the interpolants.
   *
   * @param interpolants the interpolants
   * @return Information about the counterexample, including the predicates.
   */
  private <T> CounterexampleTraceInfo<I> extractPredicates(
      List<Formula> interpolants) {

    // the counterexample is spurious. Extract the predicates from
    // the interpolants

    CounterexampleTraceInfo<I> info = new CounterexampleTraceInfo<I>();
    int i = 1;
    ////System.out.println(interpolants.size());
    for (Formula itp : interpolants) {
      I preds;
      //System.out.println(i+"=>itp=>"+itp);
      if (itp.isTrue()) {
        logger.log(Level.ALL, "For step", i, "got no interpolant.");
        preds = getTrueInterpolant();

      } else {
        logger.log(Level.ALL, "For step", i, "got:", "interpolant", itp);
        preds = convertInterpolant(itp, i);
      }
      info.addPredicatesForRefinement(preds);
      i++;
    }
    return info;
  }

  protected abstract I convertInterpolant(Formula itp, int step);

  protected abstract I getTrueInterpolant();

  /**
   * Get information about the error path from the solver after the formulas
   * have been proved to be satisfiable.
   *
   * @param f The list of formulas on the path.
   * @param pItpProver The solver.
   * @param elementsOnPath The ARGElements of the paths represented by f.
   * @return Information about the error path, including a satisfying assignment.
   * @throws CPATransferException
   * @throws InterruptedException
   */
  private <T> CounterexampleTraceInfo<I> getErrorPath(List<Formula> f,
      InterpolatingTheoremProver<T> pItpProver, Set<ARGState> elementsOnPath)
      throws CPATransferException, InterruptedException {

    // get the branchingFormula
    // this formula contains predicates for all branches we took
    // this way we can figure out which branches make a feasible path
    Formula branchingFormula = pmgr.buildBranchingFormula(elementsOnPath);

    if (branchingFormula.isTrue()) { return new CounterexampleTraceInfo<I>(f, getModel(pItpProver),
        Collections.<Integer, Boolean> emptyMap()); }

    // add formula to solver environment
    pItpProver.addFormula(branchingFormula);

    // need to ask solver for satisfiability again,
    // otherwise model doesn't contain new predicates
    boolean stillSatisfiable = !pItpProver.isUnsat();

    if (stillSatisfiable) {
      Model model = getModel(pItpProver);
      return new CounterexampleTraceInfo<I>(f, model, pmgr.getBranchingPredicateValuesFromModel(model));

    } else {
      // this should not happen
      logger.log(Level.WARNING,
          "Could not get precise error path information because of inconsistent reachingPathsFormula!");

      dumpInterpolationProblem(f);
      File dumpFile = formatFormulaOutputFile("formula", f.size());
      fmgr.dumpFormulaToFile(branchingFormula, dumpFile);

      return new CounterexampleTraceInfo<I>(f, new Model(fmgr), Collections.<Integer, Boolean> emptyMap());
    }
  }

  private <T> Model getModel(InterpolatingTheoremProver<T> pItpProver) {
    try {
      return pItpProver.getModel();
    } catch (SolverException e) {
      logger.log(Level.WARNING, "Solver could not produce model, variable assignment of error path can not be dumped.");
      logger.logDebugException(e);
      return new Model(fmgr); // return empty model
    }
  }

  public CounterexampleTraceInfo<I> checkPath(List<CFAEdge> pPath) throws CPATransferException {
    Formula f = pmgr.makeFormulaForPath(pPath).getFormula();

    TheoremProver thmProver = solver.getTheoremProver();
    thmProver.init();
    try {
      thmProver.push(f);
      if (thmProver.isUnsat()) {
        return new CounterexampleTraceInfo<I>();
      } else {
        return new CounterexampleTraceInfo<I>(Collections.singletonList(f), getModel(thmProver),
            ImmutableMap.<Integer, Boolean> of());
      }
    } finally {
      thmProver.reset();
    }
  }

  private <T> Model getModel(TheoremProver thmProver) {
    try {
      return thmProver.getModel();
    } catch (SolverException e) {
      logger.log(Level.WARNING, "Solver could not produce model, variable assignment of error path can not be dumped.");
      logger.logDebugException(e);
      return new Model(fmgr); // return empty model
    }
  }


  /**
   * Helper method to dump a list of formulas to files.
   */
  private void dumpInterpolationProblem(List<Formula> f) {
    int k = 0;
    for (Formula formula : f) {
      File dumpFile = formatFormulaOutputFile("formula", k++);
      fmgr.dumpFormulaToFile(formula, dumpFile);
    }
  }

  protected File formatFormulaOutputFile(String formula, int index) {
    if (dumpInterpolationProblems) {
      return fmgr.formatFormulaOutputFile("interpolation", stats.cexAnalysisTimer.getNumberOfIntervals(), formula,
          index);
    } else {
      return null;
    }
  }




  private <T> List<Formula> getInterpolants1(
      InterpolatingTheoremProver<T> pItpProver, List<T> itpGroupsIds) {

    List<Formula> interpolants = Lists.newArrayListWithExpectedSize(itpGroupsIds.size() - 1);

    // The counterexample is spurious. Get the interpolants.

    // how to partition the trace into (A, B) depends on whether
    // there are function calls involved or not: in general, A
    // is the trace from the entry point of the current function
    // to the current point, and B is everything else. To implement
    // this, we keep track of which function we are currently in.
    // if we don't want "well-scoped" predicates, A always starts at the beginning
    Deque<Integer> entryPoints = null;
    if (wellScopedPredicates) {
      entryPoints = new ArrayDeque<Integer>();
      entryPoints.push(0);
    }

    ////System.out.println("interpolants----------");//求插值，加插值公式,只求一次
    //System.out.println("pItpProver"+pItpProver.getClass().toString());
    for (int i = itpGroupsIds.size() - 4 >= 0 ? itpGroupsIds.size() - 4 : 0; i < itpGroupsIds.size() - 1; ++i) {
      // last iteration is left out because B would be empty
      ////System.out.println("itpIds=>"+itpGroupsIds.get(i));
      final int start_of_a = (wellScopedPredicates ? entryPoints.peek() : 0);
      logger.log(Level.ALL, "Looking for interpolant for formulas from",
          start_of_a, "to", i);
      stats.cexAnalysisSolverTimer.start();
      Formula itp = pItpProver.getInterpolant(itpGroupsIds.subList(start_of_a, i + 1));
      stats.cexAnalysisSolverTimer.stop();

      if (dumpInterpolationProblems) {
        File dumpFile = formatFormulaOutputFile("interpolant", i);
        fmgr.dumpFormulaToFile(itp, dumpFile);
      }
      // //System.out.println(itp);
      interpolants.add(itp);

      // TODO wellScopedPredicates have been disabled

      // TODO the following code relies on the fact that there is always an abstraction on function call and return

      // If we are entering or exiting a function, update the stack
      // of entry points
      // TODO checking if the abstraction node is a new function
      //        if (wellScopedPredicates && e.getAbstractionLocation() instanceof FunctionEntryNode) {
      //          entryPoints.push(i);
      //        }
      // TODO check we are returning from a function
      //        if (wellScopedPredicates && e.getAbstractionLocation().getEnteringSummaryEdge() != null) {
      //          entryPoints.pop();
      //        }
    }

    return interpolants;
  }

  public void long_exchange(Map<Pair<String, String>, CFAEdge> pe, Proposition proposition, CFAEdge edge)
      throws ParserException {
    Map<Pair<String, String>, String> props = proposition.getPropositions();
    String arrSubVal = null;//注意：初试化问题，给下面的secondT=secondT.replaceAll(arrName,String.valueOf(arrSubVal));有关，必须初始化
    String arrLen = null;
    String arrName = null;




    //1.得到数组下标值=================================================================龙开始
    switch (edge.getEdgeType()) {
    case FunctionCallEdge:
      break;//待解决=======================================方法调用中用到声明数组，得考虑
    case DeclarationEdge:
      CDeclarationEdge declarationEdge = (CDeclarationEdge) edge;
      String function = "";
      CType type = declarationEdge.getDeclaration().getType();

      arrName = declarationEdge.getDeclaration().getName();
      if (type instanceof CArrayType) {
        CArrayType arr = (CArrayType) declarationEdge.getDeclaration().getType();
        arrLen = arr.getLength().toASTString();

      }
      break;
    case StatementEdge:
      CStatementEdge statementEdge = (CStatementEdge) edge;
      CStatement expression = statementEdge.getStatement();
      if (expression instanceof CAssignment) {
        CAssignment assignmentExp = (CAssignment) expression;
        CExpression op1 = assignmentExp.getLeftHandSide();
        if (op1 instanceof CArraySubscriptExpression) {
          CIdExpression arrSubExp = (CIdExpression) ((CArraySubscriptExpression) op1).getArrayExpression();
          arrSubVal = ((CArraySubscriptExpression) op1).getSubscriptExpression().toASTString();
          arrName = arrSubExp.getName();
        }

      }


    }
    //龙结束===========================================================================龙结束
    List<CFAEdge> listCFAEdeg = new ArrayList<CFAEdge>(pe.values());
    for (int i = 0; i < listCFAEdeg.size(); i++) {
      String newStr = listCFAEdeg.get(i).getCode().replaceAll(arrName, arrSubVal);


      /*CFAEdge cfaEdge=listCFAEdeg.get(i);
      String cfaEdgeStr=cfaEdge.getCode();
      CFAEdge newcfaEdgeStr= (CFAEdge)cfaEdgeStr.replaceAll(arrName,arrSubVal);
      listCFAEdeg.set(i,newcfaEdgeStr);*/
    }


    //2.得到四个d，!d,r,！r
    List<Pair<String, String>> list = new ArrayList<Pair<String, String>>(props.keySet());
    String global = "";
    if (proposition.getGlobalVar().size() != 0) {
      for (String s : proposition.getGlobalVar()) {
        global = global + "int " + s + ";\n";
      }
    }
    String[] statements = { "", "" };


    //3.对四个命题进行处理===================================
    //用statements[0]存r与d，用statements[1]存!r!d=====让r与d结合，!r和!d结合=======[blkNum!=0&&blkNum==blkNum&&, !(blkNum==blkNum)&&!(blkNum!=0)&&]
    for (int i = 0; i < list.size(); i++) {
      //龙测试
      Pair<String, String> pl = list.get(i);
      String firstT = pl.getFirst();//第一个：!r====第二个：r=====第三个：d
      if (pl.getFirst().equals("d") || pl.getFirst().equals("!d")) {

        String secondT = pl.getSecond();
        secondT = secondT.replaceAll(arrName, arrSubVal);
        pl = Pair.of(firstT, secondT);
        list.set(i, pl);
      }
      //龙测试结束

      if (!pl.getFirst().startsWith("!"))
        statements[0] = statements[0] + pl.getSecond() + "&&";
      else
        statements[1] = statements[1] + pl.getSecond() + "&&";
    }
    /* Map<Pair<String,String>,CFAEdge> pEdges=new HashMap<Pair<String,String>,CFAEdge>();

     for(int i=0;i<2;i++){
       String statement=statements[i];
       statement=statement.substring(0,statement.lastIndexOf("&&")).trim();
       String[] ss=statement.split("&&");//i=0时ss得到[blkNum!=0, blkNum==blkNum]
       for(int j=0;j<ss.length;j++){
       statement=ss[j];

       String statement1="int main(){if("+statement+");}";
       ParseResult myString=parser.parseString(global+statement1);
       Map<String, FunctionEntryNode> fn=myString.getFunctions();
       CFANode node=fn.get("main");
       while(node.getNumLeavingEdges()!=0){
         if(node.getNumLeavingEdges()==1){
           node=node.getLeavingEdge(0).getSuccessor();
           continue;
         }
         List<CFAEdge> edges=node.getLeavingEdge();
         boolean tb=false;
         for(CFAEdge e:edges){
           for(Pair<String,String> p:list)
            if(e.getRawStatement().equals("["+statement+"]")&&statement.equals(p.getSecond())){
              if(statement.contains("==")){
                String s[]=statement.split("==");
                if(s[0].startsWith("!(")){
                  s[0]=s[0].substring(2);
                  s[1]=s[1].substring(0,s[1].length()-1);
                }
                if(!(s.length==2&&s[0].equals(s[1]))){
                  pEdges.put(p, e);
                }
              }
              else{
               pEdges.put(p, e);
              }
             tb=true;
             node=e.getSuccessor();
             break;
           }
           if(tb){
             break;
           }
         }
       }
      }
     }

    return pEdges;*/
  }

  public int generateOneStepFormula(List<Formula> formulas, PathFormula pathFormula, CFAEdge sucEdge,
      Transition transition, Proposition proposition) {
    int count = 0;
    String curTerm = transition.getLabel().trim();
    //String nextTerm = transition.getTarget_state();
    curTerm = curTerm.replaceAll("[\\(|\\)| ]", "");
    String curTerms[] = curTerm.split("&&");
    //PathFormula sucPath=null;
    if (sucEdge instanceof CFunctionCallEdge) {
      sucEdge = ((CFunctionCallEdge) sucEdge).getSummaryEdge();
    }
    //formulas.add(pathFormula.getFormula());
    for (int i = 0; i < curTerms.length; i++) {
      String subCurTerm = curTerms[i].trim();
      if (subCurTerm.equals("false")) {

      }
      else if (!subCurTerm.equals("true")) {
        Map<Pair<String, String>, CFAEdge> propos = proposition.getPropEdges();
        Iterator<Pair<String, String>> iterator = propos.keySet().iterator();
        while (iterator.hasNext()) {
          Pair<String, String> next = iterator.next();
          if (next.getFirst().equals(subCurTerm)) {
            CFAEdge e = propos.get(next);
            if (e != null) {
              e.setPredecessor(sucEdge.getPredecessor());
              e.setSuccessor(sucEdge.getSuccessor());
              //e.setSuccessor(sucNode.getNumLeavingEdges()!=0?sucNode.getLeavingEdge(0).getSuccessor():sucNode);
              try {
                PathFormula p = pmgr.makeAnd1(pathFormula, e);
                pathFormula = p;
                formulas.add(p.getFormula());
                count++;
                break;
              } catch (CPATransferException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
              }
            }
          }
        }
      }
    }
    return count;
  }

}