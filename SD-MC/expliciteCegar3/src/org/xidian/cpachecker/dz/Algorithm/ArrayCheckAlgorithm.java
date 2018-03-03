/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.xidian.cpachecker.dz.Algorithm;


/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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


import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.logging.Level;

import org.sosy_lab.common.Classes;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.algorithm.MyAlgorithm;
import org.sosy_lab.cpachecker.core.defaults.SimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment.Action;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGSimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.InvalidComponentException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.xidian.cpachecker.dz.MyCPA;
import org.xidian.cpachecker.dz.Proposition;
import org.xidian.cpachecker.dz.proposition.PropositionInfo;
import org.xidian.crl.CRLGlobal;

import com.google.common.base.Throwables;
import com.google.common.collect.Iterables;
import com.songstan.ltl_trans.jni.NFGJni;
import com.songstan.ltl_trans.method.Transition;

@Options(prefix = "array")
public class ArrayCheckAlgorithm implements MyAlgorithm, StatisticsProvider {

  private final ConfigurableProgramAnalysis cpa;
  private final TransferRelation transferRelation;
  private final LogManager logger;
  private Refiner mRefiner;
  private final PrecisionAdjustment precisionAdjustment;
  @Option(required = true,
      description = "Which refinement algorithm to use? "
          + "(give class name, required for PointerCheck) If the package name starts with "
          + "'org.sosy_lab.cpachecker.', this prefix can be omitted.")
  @ClassOption(packagePrefix = "org.sosy_lab.cpachecker")
  private Class<? extends Refiner> refiner = null;

  private MyCPA myCpa;
  private Map<String, List<Transition>> nf = new HashMap<String, List<Transition>>();//跟性质有关
  private Map<Transition, List<Integer>> map = new HashMap<Transition, List<Integer>>();
  private Transition trueTrans = new Transition("true", "true", "true");
  private int max = 0;
  private Set<Integer> used = new HashSet<Integer>();
  //private Set<Integer> utilFlag = new HashSet<Integer>();
  private List<ARGState> covered = new ArrayList<ARGState>();
  private List<ARGState> selfLoop = new ArrayList<ARGState>();
  private List<Integer> allMy = new ArrayList<Integer>();
  private String fs = "";
  public static boolean remove = false;
  //public static Set<Integer> set=new HashSet<Integer>();
  public static ARGState rs = null;

  public static int index = -1;
  private final String checkType = "arraycheck";
  private Stack<Map<String, Integer>> stack = new Stack<Map<String, Integer>>();
  private Map<String, Integer> global = new HashMap<String, Integer>();
  private Configuration config;
  public ArrayCheckAlgorithm(Configuration config, final ConfigurableProgramAnalysis cpa, LogManager pLogger)
      throws CPAException, InvalidConfigurationException {
    this.config=config;
    config.inject(this);
    this.cpa = cpa;
    //transferRelation = myCpa.getTransferRelation();
    logger = pLogger;
    //precisionAdjustment = myCpa.getPrecisionAdjustment();
    mRefiner = createInstance(cpa);
    //
    transferRelation = cpa.getTransferRelation();
    PrecisionAdjustment wrappedPrec = cpa.getPrecisionAdjustment();
    if (wrappedPrec instanceof SimplePrecisionAdjustment) {
      precisionAdjustment = new ARGSimplePrecisionAdjustment((SimplePrecisionAdjustment) wrappedPrec);
    } else {
      precisionAdjustment = cpa.getPrecisionAdjustment();
    }
  }

  private Refiner createInstance(ConfigurableProgramAnalysis pCpa) throws CPAException, InvalidConfigurationException {
    //config.inject(this);
    // get factory method
    System.out.println("创建CEGAR");
    Method factoryMethod;
    try {
      factoryMethod = refiner.getMethod("create", ConfigurableProgramAnalysis.class);
    } catch (NoSuchMethodException e) {
      throw new InvalidComponentException(refiner, "Refiner",
          "No public static method \"create\" with exactly one parameter of type ConfigurableProgramAnalysis.");
    }

    // verify signature
    if (!Modifier.isStatic(factoryMethod.getModifiers())) { throw new InvalidComponentException(refiner, "Refiner",
        "Factory method is not static"); }

    String exception =
        Classes.verifyDeclaredExceptions(factoryMethod, CPAException.class, InvalidConfigurationException.class);
    if (exception != null) { throw new InvalidComponentException(refiner, "Refiner",
        "Factory method declares the unsupported checked exception " + exception + "."); }

    // invoke factory method
    Object refinerObj;
    try {
      refinerObj = factoryMethod.invoke(null, pCpa);

    } catch (IllegalAccessException e) {
      throw new InvalidComponentException(refiner, "Refiner", "Factory method is not public.");

    } catch (InvocationTargetException e) {
      Throwable cause = e.getCause();
      Throwables.propagateIfPossible(cause, CPAException.class, InvalidConfigurationException.class);

      throw new UnexpectedCheckedException("instantiation of refiner " + refiner.getSimpleName(), cause);
    }

    if ((refinerObj == null) || !(refinerObj instanceof Refiner)) { throw new InvalidComponentException(refiner,
        "Refiner", "Factory method did not return a Refiner instance."); }

    return (Refiner) refinerObj;
  }


  public Map<Pair<String, String>, CFAEdge> propositionToCFAEdge(Proposition proposition) throws ParserException {
    Map<Pair<String, String>, String> props = proposition.getPropositions();
    List<Pair<String, String>> list = new ArrayList<Pair<String, String>>(props.keySet());
    String global = "";
    if (proposition.getGlobalVar().size() != 0) {
      for (String s : proposition.getGlobalVar()) {
        global = global + "int " + s + ";\n";
      }
    }
    String[] statements = { "", "" };
    for (Pair<String, String> pl : list) {
      if (!pl.getFirst().startsWith("!"))
        statements[0] = statements[0] + pl.getSecond() + "&&";
      else
        statements[1] = statements[1] + pl.getSecond() + "&&";
    }
    Map<Pair<String, String>, CFAEdge> pEdges = new HashMap<Pair<String, String>, CFAEdge>();

    for (int i = 0; i < 2; i++) {
      String statement = statements[i];
      statement = statement.substring(0, statement.lastIndexOf("&&")).trim();
      String[] ss = statement.split("&&");
      for (int j = 0; j < ss.length; j++) {
        statement = ss[j];

        String statement1 = "int main(){if(" + statement + ");}";
        ParseResult myString = MyCPA.parser.parseString(/*global + */statement1);
        Map<String, FunctionEntryNode> fn = myString.getFunctions();
        CFANode node = fn.get("main");
        while (node.getNumLeavingEdges() != 0) {
          if (node.getNumLeavingEdges() == 1) {
            node = node.getLeavingEdge(0).getSuccessor();
            continue;
          }
          List<CFAEdge> edges = node.getLeavingEdge();
          boolean tb = false;
          for (CFAEdge e : edges) {
            for (Pair<String, String> p : list)
              if (e.getRawStatement().equals("[" + statement + "]") && statement.equals(p.getSecond())) {
                if (statement.contains("==")) {
                  String s[] = statement.split("==");
                  if (s[0].startsWith("!(")) {
                    s[0] = s[0].substring(2);
                    s[1] = s[1].substring(0, s[1].length() - 1);
                  }
                  if (!(s.length == 2 && s[0].equals(s[1]))) {
                    pEdges.put(p, e);
                  }
                }
                else {
                  pEdges.put(p, e);
                }
                tb = true;
                node = e.getSuccessor();
                break;
              }
            if (tb) {
              break;
            }
          }
        }
      }
    }

    return pEdges;
  }

  public void run1(ReachedSet reachedSet, Proposition proposition) throws ParserException, CPATransferException {
    Map<Pair<String, String>, CFAEdge> pEdges = propositionToCFAEdge(proposition);
    proposition.setPropEdges(pEdges);
  }
  public static  List<Proposition> run2(Proposition proposition,CFAEdge rEdge) throws ParserException, CPATransferException{
    PropositionInfo.getInstance();
    //把d与!d转化成边============={(d, blkNum!=0)=Line 1: N666 -{[blkNum != 0]}-> N668, (!d, !(blkNum!=0))=Line 1:  N681 -{[!(blkNum != 0)]}-> N683}
    List<Map<Pair<String,String>,CFAEdge>> pEdges=PropositionInfo.long_propositionToCFAEdge(proposition,rEdge);
    List<Proposition> propositions = new ArrayList<Proposition>();
    Proposition saveproposition1=new Proposition();
    Proposition saveproposition2=new Proposition();
    int i=0;
    for(Map<Pair<String,String>,CFAEdge> pEdge:pEdges){

      if(i==0){
        saveproposition1.setPropEdges(pEdge);
        propositions.add(saveproposition1);
      }else if(i==1){
        saveproposition2.setPropEdges(pEdge);
     propositions.add(saveproposition2);
     }
     i++;
    }

    return propositions;
  }

  @Override
  public Pair<ARGState, ARGState> run(final ReachedSet reachedSet, Proposition proposition, Set<CFANode> loopHeadNode,
      CFA cfa)
      throws InterruptedException, CPAException,
      IOException, InvalidConfigurationException {
    final StopOperator stopOperator = cpa.getStopOperator();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    int ref = 0;
    int ref1 = 0;
    int level = 0;//标记,用来求覆盖
    int i = 0;
    String var = "p";
    NFGJni jni = new NFGJni();
    Pair<ARGState, ARGState> errorState = null;//if UNSAFE then the first ARGState whose property is true
    //boolean flag=true;
    boolean isTwo = true;//判断后继个数是否为2
    boolean firstB = true;
    map.put(new Transition("true", "true", "true"), new ArrayList<Integer>());
    Proposition non = proposition.negative();

    AbstractState first = reachedSet.getFirstState();
    FileReader fr = new FileReader("D:\\property\\properties.txt");
    assert fr != null;
    BufferedReader br = new BufferedReader(fr);
    String ps = "";
    String s;
    while ((s = br.readLine()) != null) {
      ps = ps + s;
    }
    br.close();
    ((ARGState) first).setProperties(ps);
    ((ARGState) first).setProposition(non);
    boolean over = false;
    int spu = 0;
    long time = System.currentTimeMillis();
    //初始化性质信息，方便测试

    //initProperty(nf);
    while (!over) {
      System.gc();
      System.out.println("goingon");
      reachedSet.setResult(Result.SAFE);
      covered.clear();
      selfLoop.clear();
      // flag=true;
      //      if(ref==6)
      //        break;
      firstB = true;
      i = 1;
      spu = 0;
      errorState = null;//用于保存一些输出结果信息
      while (reachedSet.hasWaitingState() && spu == 0) {
        i = i + 1;
        CPAchecker.stopIfNecessary();
        long time1 = System.currentTimeMillis();
        // Pick next state using strategy
        // BFS, DFS or top sort according to the configuration
        final ARGState state = (ARGState) reachedSet.popFromWaitlist();
        final Precision precision = reachedSet.getPrecision(state);
        if (state.isDestroyed()) {
          reachedSet.removeAll(state.getSubgraph());
          reachedSet.remove(state);
          continue;
        }
        //level = state.getLevel();

        CFANode loc = AbstractStates.extractLocation(state);
        state.setLoc(loc);
        //龙==============================================方法调用处理减少层数问题：：：：
        /*int temp1= CRLGlobal.getInstance().getFunFlgLen();
        List<String> temp2=CRLGlobal.getInstance().getFunLenList();
        List<Integer> temp3=CRLGlobal.getSucnodenubs();*/
         if(!CRLGlobal.getSucnodenubs().isEmpty()){

           for(int j=0;j<CRLGlobal.getSucnodenubs().size();j++){
         if(loc.getNodeNumber()==CRLGlobal.getSucnodenubs().get(j)){
           int temp=CRLGlobal.getInstance().getFunFlgLen();
           if(temp!=0){
           //System.out.println("chubian变数"+temp);
             CRLGlobal.getFuntwoarrflag().remove(temp-1);
           CRLGlobal.getInstance().setFunFlgLen(temp-1);
           CRLGlobal.getSucnodenubs().remove(j);

           CRLGlobal.getInstance();
         //System.out.println(CRLGlobal.getInstance().getFunLenList());
         CRLGlobal.getFunLenList().remove(temp-1);
         CRLGlobal.getLeftfunarrlenList().remove(temp-1);
         }

         }
           }
         }

         //减少层数减少结束=====================================================================
         FileReader fr1;
         try {
           fr1 = new FileReader("D:\\property\\propositions.txt");
           assert fr1!=null;
           BufferedReader br1=new BufferedReader(fr1);
           String ps1="";
           String s1;
           while((s1=br1.readLine())!=null){
               ps1=ps1+s1;
              // System.out.println(ps);
           }
           br1.close();

           proposition=new Proposition(ps1);
           PropositionInfo.getInstance().propositionToCFAEdgeForArray(logger, config, proposition);

         } catch (FileNotFoundException e1) {
           // TODO Auto-generated catch block
           e1.printStackTrace();
         } catch (IOException e1) {
           // TODO Auto-generated catch block
           e1.printStackTrace();
         } catch (ParserException e) {
           // TODO Auto-generated catch block
           e.printStackTrace();
         }
        //System.out.println("N"+loc.getNodeNumber());


        if (state.getStateId() == 221)
          i = i + 1 - 1;
        if (loc.getNodeNumber() == 23694)
          i = i + 1 - 1;
        System.out.println(i + "," + "," + state.getStateId() + "," + "N" + loc.getNodeNumber());
        logger.log(Level.FINER, "Retrieved state from waitlist");
        logger.log(Level.ALL, "Current state is", state, "with precision",
            precision);
        List<Transition> newProperties = getProperties(state, jni);//展开性质,并计算下一个状态可以满足的性质
        if (newProperties == null || newProperties.size() == 0) {
          state.setFalse(true);
          continue;
        }

        if (firstB) {//第一次
          state.setUtil(map.get(state.getProperties()));
          firstB = false;
        }
        for (int j = 0; j < newProperties.size(); j++) {//一个状态只能有一个性质,所以分开操作
          //List<String> curProperties=new ArrayList<>();
          Transition curProperties = newProperties.get(j);
          List<Integer> curUtil = map.get(curProperties);
          Collection<? extends AbstractState> successors =
              transferRelation.getAbstractSuccessors(state, precision, null);
          // TODO When we have a nice way to mark the analysis result as incomplete,
          // we could continue analysis on a CPATransferException with the next state from waitlist.
          int numSuccessors = successors.size();
          logger.log(Level.FINER, "Current state has", numSuccessors,
              "successors");
          if (numSuccessors == 1) {
            isTwo = false;
          }
          else if (numSuccessors == 2) {
            isTwo = true;
          }
          else {
            //c程序结束,最后一个状态自循环
            if (loc.getNumLeavingEdges() == 0 && !selfLoop.contains(state)) {
              //  CFAEdge edge = new BlankEdge("loop", loc.getLineNumber(), loc, loc, "loop");
              //  loc.addEnteringEdge(edge);
              //  loc.addLeavingEdge(edge);
              //  state.addParent(state);
              //  state.setForlumas(null);
              //  selfLoop.add(state);
              spu = findCounterexampleSelfLoop(state, reachedSet);
              if (spu == 1)
                break;
            }
            continue;
          }
          for (AbstractState successor : Iterables.consumingIterable(successors)) {
            logger.log(Level.FINER, "Considering successor of current state");
            logger.log(Level.ALL, "Successor of", state, "\nis", successor);
            Triple<AbstractState, Precision, Action> precAdjustmentResult =
                precisionAdjustment.prec(successor, precision, reachedSet);
            successor = precAdjustmentResult.getFirst();
            Precision successorPrecision = precAdjustmentResult.getSecond();
            Action action = precAdjustmentResult.getThird();
            if (action == Action.BREAK) {
              reachedSet.setResult(Result.SAFE);
              Runtime rt = Runtime.getRuntime();
              System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
              return errorState;

            }
            ((ARGState) successor).copyVarInfos(state.stack);
            ((ARGState) successor).setLevel(level);
            ((ARGState) successor).setProposition(state.getProposition());
            //List<Formula> fft = state.getFormulas();
            ((ARGState) successor).setForlumas(state.getFormulas());
            CounterexampleInfo cexInfo =
                mRefiner.performRefinementForProperty(successor, proposition, checkType, isTwo);
            ((ARGState) successor).setProposition(cexInfo.getProposition());
            ((ARGState) successor).setProperties(curProperties.getTarget_state());
            ((ARGState) successor).setTransition(curProperties);
            ((ARGState) successor).setUtil(curUtil);

            if (curProperties.equals("true") && errorState == null) {
              errorState = Pair.of(state, (ARGState) successor);
            }
            Collection<AbstractState> reached = reachedSet.getReached(successor);
            // An optimization, we don't bother merging if we know that the
            // merge operator won't do anything (i.e., it is merge-sep).
            /* if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()&&merge) {
               System.out.println("进来了");
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

                   toRemove.add(reachedState);
                   toAdd.add(Pair.of(mergedState, successorPrecision));
                 }
               }
               reachedSet.removeAll(toRemove);
               reachedSet.addAll(toAdd);
             }*/
            boolean stop = stopOperator.stop(successor, reached, precision);//cpachecker自身求覆盖,加入新的限制
            //System.out.println(((ARGState) successor).getLoc());
            if (!stop) {
              reachedSet.add(successor, successorPrecision);
              computeFlag(state, (ARGState) successor, curUtil);
            } else {
              computeFlag(state, (ARGState) successor, curUtil);
              spu = findCounterexampleCovered((ARGState) successor, reachedSet);
              if (spu == 1) {
                reachedSet.add(successor, successorPrecision);
                break;
              }
            }
            logger.log(Level.FINER,
                "No need to stop, adding successor to waitlist");
          }
        }
        state.setForlumas(null);
      }
      //do{
      //int spu=findCounterexample(reachedSet);
      if (spu == 0) {
        reachedSet.setResult(Result.SAFE);
        Runtime rt = Runtime.getRuntime();
        System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
        System.out.println("细化了" + ref + "次,ref1=" + ref1);
        return errorState;
      }
      //refine call
      logger.log(Level.FINE, "Error found, performing CEGAR");
      ref += 1;
      if (ref == 3)
        i = i + 1;
      boolean refinementResult;
      try {
        refinementResult = mRefiner.performRefinement(reachedSet);//analysis
      } catch (RefinementFailedException e) {
        throw e;
      }

      logger.log(Level.FINE, "Refinement successful:", refinementResult);

      if (refinementResult) {
        covered.clear();
        selfLoop.clear();
        spu = 0;
      }
      else {
        reachedSet.setResult(Result.UNSAFE);
        ((ARGState) reachedSet.getLastState()).setMyTarget(true);
        reset();
        Runtime rt = Runtime.getRuntime();
        System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
        return errorState;
      }
      //}while(covered.size()!=0||selfLoop.size()!=0);
    }
    reset();
    Runtime rt = Runtime.getRuntime();
    System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
    return errorState;
  }



  private Proposition computeProposition(Stack<Map<String, Integer>> stack, Map<String, Integer> global, String var,
      Proposition proposition, CFAEdge edge) {
    // TODO Auto-generated method stub
    Proposition p = new Proposition();
    String locfunction = edge.getPredecessor().getFunctionName();
    String funcname = proposition.getFuncname();
    String d = "!d";
    String r = "!r";
    if (funcname.equals("Global")) {
      if (global.keySet().contains(var) && global.get(var) == 1) {
        d = "d";
      }
      else {
        d = "!d";
      }
    }
    else if (funcname.equals(locfunction)) {
      Map<String, Integer> top = stack.peek();
      if (top.keySet().contains(var) &&top.get(var) == 1) {
        d = "d";
      }
      else {
        d = "!d";
      }
    }
    boolean myjudge = CFAUtils.judge(edge, var);
    if(myjudge){
      r="r";
    }else{
      r="!r";
    }
    p.setdAndr(Pair.of(d,r));
    return p;
  }

  private void staticCFAEdge(CFAEdge edge) {
    // TODO Auto-generated method stub
    edge.analysisCFAEdge(stack, global);
  }

  private void addRelation(CFANode pre, CFANode suc) {
    //CFAEdge preToSuc=pre.getEdgeTo(suc);
    CFAEdge blankEdge = new BlankEdge("BLANKEDGE", pre.getLineNumber(), pre, suc, "myblank");
    pre.getLeavingEdge().add(blankEdge);
    suc.getEnteringEdges().add(blankEdge);
  }

  private int findCounterexampleCovered(ARGState state, ReachedSet reached) {

    // covered.remove(state);
    ARGState covering = state.getCoveringState();
    Path p1 = ARGUtils.getOnePathToARGState(state, covering);
    if (p1 == null) { return 0; }
    p1 = null;
    Set<Integer> utilFlag = new HashSet<Integer>();
    ARGUtils.getOnePathTo(state, utilFlag);
    //Iterator<Integer> itFlag = utilFlag.keySet().iterator();
    boolean isCex = false;
    if (utilFlag.equals(allMy))
      isCex = true;
    //     boolean isNULL = true;
    //     while (itFlag.hasNext()) {
    //       isNULL = true;
    //       Collection<Integer> next = utilFlag.get(itFlag.next());
    //       if (next.size() == 1)
    //         break;
    //       Iterator<ARGState> iterator = path.getStateSet().iterator();
    //       while (iterator.hasNext()) {
    //         int stateId = iterator.next().getStateId();
    //         if (next.contains(stateId)) {
    //           isNULL = false;
    //           break;
    //         }
    //       }
    //       if (isNULL)
    //         break;
    //     }
    //     isCex = isNULL ? false : true;

    if (isCex) {

      reached.setLastState(state.getCoveringState());
      return 1;
    }
    return 0;

  }

  private int findCounterexampleSelfLoop(ARGState state, ReachedSet reached) {
    //selfLoop.remove(state);
    if (state.getFlag().equals(allMy)) {
      reached.setLastState(state);
      state.setMyTarget(true);
      return 1;
    }
    return 0;
  }

  private void reset() {
    // TODO Auto-generated method stub
    map = null;
    used = null;
    nf = null;
  }

  private void computeFlag(ARGState curState, ARGState successor, List<Integer> util) {
    // TODO Auto-generated method stub
    List<Integer> curFlag = new ArrayList<Integer>();
    if (util == null)
      successor.setFlag(allMy);
    else {
      for (Integer integer : allMy) {
        if (!util.contains(integer)) {
          curFlag.add(integer);
          //utilFlag.put(integer, successor.getStateId());
        }
      }
      successor.setFlag(curFlag);
    }
  }

  private boolean mystop(ARGState state, ARGState itNext) {
    // TODO Auto-generated method stub
    //boolean result=false;
    Proposition sucP = state.getProposition();
    String sucProperty = state.getProperties();
    Map<Pair<String, String>, String> sucPros = sucP.getPropositions();
    Set<Pair<String, String>> sucSet = sucPros.keySet();
    Set<Pair<String, String>> set = itNext.getProposition().getPropositions().keySet();
    String setProperty = itNext.getProperties();
    if (set.equals(sucSet) && sucProperty.equals(setProperty)) {
      state.getChildren().clear();
      covered.add(state);
      return true;
    }
    else {
      state.uncover();
      return false;
    }
  }

  private List<Transition> getProperties(AbstractState curState, NFGJni jni) {
    // TODO Auto-generated method stub
    //boolean bool=true;
    String curPro = ((ARGState) curState).getProperties();//范式
    List<Transition> newPro = new ArrayList<Transition>();
    //List<Transition> newProTemp = new ArrayList<Transition>();
    //List<Integer> util=new ArrayList<>();
    if (curPro.equals("true")) {
      newPro.add(trueTrans);
      return newPro;
    }
    Set<Pair<String, String>> curPropositions = ((ARGState) curState).getProposition().getPropositions().keySet();//命题
    List<Transition> tmpList = new ArrayList<Transition>();
    if (nf.keySet().contains(curPro)) {
      tmpList = nf.get(curPro);
    }
    else {
      //NFGJni jni = new NFGJni(curPro); //展开ltl性质
      jni.process(curPro);
      String source = getNFUtilFlag(jni);
      tmpList = jni.get_resutl();
      nf.put(source, tmpList);
    }
    Iterator<Transition> itTmp = tmpList.iterator();
    while (itTmp.hasNext()) { //性质的展开项            //求交集:将ARG的当前状态满足的命题与性质的当前状态求交
      //Set<Transition> newProTemp = new HashSet<Transition>();
      Transition t = itTmp.next();
      String label = t.getLabel(); //性质的当前状态
      label = label.replaceAll("[\\(|\\)| ]", "");
      String target = t.getTarget_state();
      Iterator<Pair<String, String>> it = curPropositions.iterator();
      while (it.hasNext()) { //ARGState满足的命题
        String prop = it.next().getFirst();
        boolean isTrue = intersection(prop, label);//求交
        if (isTrue) {
          if (target.equals("false")) {
            ((ARGState) curState).setFalse(true);
            return null;
          }
          else if (!newPro.contains(t)) {
            newPro.add(t);
          }
        }
        else {
          if (newPro.contains(t))
            newPro.remove(t);
          break;
        }
      }
      //      newPro.addAll(newProTemp);
    }
    return newPro;
  }

  /*
   * 计算U(util)标记
   */
  private String getNFUtilFlag(NFGJni jni) {
    // TODO Auto-generated method stub
    boolean f = true;
    String source = "";
    List<Integer> all = new ArrayList<Integer>();
    long head = jni.nfg_states_head();
    // long tail = jni.nfg_states_tail();
    long state = jni.nfg_stateNxt(head);
    //for (long state = jni.nfg_stateNxt(head); state != tail; state = jni.nfg_stateNxt(state)) {
    String source_State = jni.state_string(state);
    if (source.equals(""))
      source = source_State;
    if (f) {
      fs = source_State;
      f = false;
    }
    long fin1 = jni.get_all_final();
    //System.out.println("all the trans' final is");
    for (int j = 0; j < 32; j++) {
      if ((fin1 & (1 << j)) > 0) {
        //System.out.print(j+" ");
        all.add(j);
        if (!allMy.contains(j))
          allMy.add(j);
      }
    }
    //if (allMy.size() == 0) {
    //allMy.addAll(all);
    //}
    // System.out.println("\n"+source_State);
    long trans = jni.nfg_stateFirstTrans(state);
    for (long t = jni.nfg_transNxt(trans); t != trans; t = jni.nfg_transNxt(t)) {
      long fin = jni.trans_final(t);
      // System.out.println("the trans' final is");
      List<Integer> tmp = new ArrayList<Integer>(all);
      for (int i = 0; i < 32; i++) { //for循环的意思
        if ((fin & (1 << i)) > 0) {
          // System.out.print(i+" ");
          tmp.remove(new Integer(i));
        }
      }
      System.out.println();
      String target_State = jni.trans__point_string(t);
      String trans_label = jni.state_trans_string(t);
      Transition one = new Transition(trans_label, source_State, target_State);
      if (!map.keySet().contains(one)) {
        map.put(one, tmp);
        jni.get_resutl().add(one);
        one.setUtil(tmp);
      }
      //result.add(one);
      System.out.println(one);
      System.out.println("......one time ....");
      //}
    }
    //Iterator<Transition> itKeyMap = tmpMap.keySet().iterator();
    //Map<Integer, Integer> tmp = new HashMap<>();
    return source_State;

    //    while (itKeyMap.hasNext()) {
    //      Transition next = itKeyMap.next();
    //      List<Integer> nv = tmpMap.get(next);
    //      if (nv.size() == 1) {
    //        int nv0 = nv.get(0);
    //        if (!map.keySet().contains(next)) {
    //          max = max < nv0 ? nv0 : max;
    //          if (used.contains(nv0)) {
    //            nv.set(0, ++max);
    //          }
    //          map.put(next, nv);
    //        }
    //        else {
    //          if (map.get(next).size() != 0) {
    //            tmp.put(nv0, map.get(next).get(0));
    //            tmpMap.put(next, map.get(next));
    //          }
    //        }
    //      }
    //      else if (nv.size() == 0) {
    //        if (!map.keySet().contains(next)) {
    //          map.put(next, nv);
    //        }
    //      }
    //    }
    //    itKeyMap = tmpMap.keySet().iterator();
    //    Set<Integer> tmpSet = tmp.keySet();
    //    while (itKeyMap.hasNext()) {
    //      String next = itKeyMap.next();
    //      List<Integer> nv = tmpMap.get(next);
    //      if (nv.size() > 1) {
    //        for (int i = 0; i < nv.size(); i++) {
    //          Integer integer = nv.get(i);
    //          if (tmpSet.contains(integer)) {
    //            nv.set(i, tmp.get(integer));
    //          }
    //        }
    //        if (!map.keySet().contains(next)) {
    //          map.put(next, nv);
    //        }
    //      }
    //    }

  }

  private final boolean intersection(String p, String q) {
    String array[] = q.split("&&");
    for (int i = 0; i < array.length; ++i) {
      String s = array[i];
      if (s.equals("!" + p) || p.equals("!" + s))
        return false;
    }
    return true;
  }

  public String appendSpace(String para) {
    int length = para.length();
    char[] value = new char[length << 1];
    for (int i = 0, j = 0; i < length; ++i, j++) {
      value[j] = para.charAt(i);
      if (!isOK(para.charAt(i))) {
        value[1 + j] = ' ';
        j++;
      }
    }
    return new String(value);
  }

  private boolean isOK(char ch) {
    // TODO Auto-generated method stub
    if (String.valueOf(ch).matches("[<|\\[|\\-|\\||&|a-z|!]")) { return true; }
    return false;
  }



  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    // TODO Auto-generated method stub

  }

  @Override
  public boolean run(ReachedSet pReachedSet) throws CPAException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }







}
