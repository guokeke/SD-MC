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


import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.cpachecker.util.AbstractStates.toState;

import java.io.BufferedReader;
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
import java.util.Random;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.Classes;
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.algorithm.MyAlgorithm;
import org.sosy_lab.cpachecker.core.defaults.SimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment.Action;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGSimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.InvalidComponentException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.xidian.cpachecker.dz.MyCPA;
import org.xidian.cpachecker.dz.Proposition;
import org.xidian.cpachecker.dz.proposition.PropositionInfo;
import org.xidian.yk.KeyVar;
import org.xidian.yk.Operators;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.songstan.ltl_trans.jni.NFGJni;
import com.songstan.ltl_trans.method.Transition;

@Options(prefix = "simpleproperty")
public class SimplePropertyCheckAlgorithm implements MyAlgorithm, StatisticsProvider {

  private CFA cfa = null;
  private final ConfigurableProgramAnalysis cpa;
  private final TransferRelation transferRelation;
  private final LogManager logger;
  private Refiner mRefiner;
  private final PrecisionAdjustment precisionAdjustment;
  @Option(
      required = true,
      description = "Which refinement algorithm to use? "
          + "(give class name, required for SimpleProperty) If the package name starts with "
          + "'org.sosy_lab.cpachecker.', this prefix can be omitted.")
  @ClassOption(packagePrefix = "org.sosy_lab.cpachecker")
  private Class<? extends Refiner> refiner = null;
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
  private Set<String> hasUnfoldProperty = new HashSet<String>();
  public static int index = -1;
  private final String checkType = "simplepropertycheck";
  private List<String> unknownVars = new ArrayList<String>();
  private long time_solve;

  public SimplePropertyCheckAlgorithm(Configuration config, final ConfigurableProgramAnalysis cpa, LogManager pLogger)
      throws CPAException, InvalidConfigurationException {
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
                } else {
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

  @Override
  public Pair<ARGState, ARGState> run(final ReachedSet reachedSet, Proposition proposition, Set<CFANode> loopHeadNode,
      CFA cfa)
      throws InterruptedException, CPAException,
      IOException, InvalidConfigurationException {
    this.cfa = cfa;
    final StopOperator stopOperator = cpa.getStopOperator();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    int ref = 0;
    int ref1 = 0;
    int level = 0;//标记,用来求覆盖
    int i = 0;
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
        ARGState state;
        if(Operators.myWaitStack.isEmpty()){
          state=(ARGState) reachedSet.popFromWaitlist();
        }
        else{
          //深度优先展开性质为true的节点
          state=(ARGState) Operators.myWaitStack.pop();
        }
        final Precision precision = reachedSet.getPrecision(state);
        if (state.isDestroyed()) {
          if (state.getChildren() != null)
            reachedSet.removeAll(state.getSubgraph());
          reachedSet.remove(state);
          continue;
        }
        //level = state.getLevel();
        if(state.getLastTerms()!=null){
          Operators.lastTerms=state.getLastTerms();
        }
        //<yangkai>
        Operators.tempKeyFormulas = state.getKeyFormulas();

        CFANode loc = AbstractStates.extractLocation(state);
        state.setLoc(loc);

        //System.out.println(state.getKeyFormulas());//打印关键路径
        if(state.getStateId()==10025){
          i = i + 1 - 1;
        }
        if (loc.getNodeNumber()==5631){
          i = i + 1 - 1;
          //KeyVar.loc.remove(loc.getNodeNumber());
        }
        if(Operators.time_solve3>2000){
          KeyVar.tmp=true;
          i=i+1-1;
        }
        //输出状态
        System.out.println(i + "," + "," + state.getStateId() + "," + "N" + loc.getNodeNumber());//+","+Operators.time_solve1
        //    +","+Operators.time_solve+","+Operators.time_solve2+","+Operators.time_solve3+","+Operators.time_solve4);
        Operators.time_solve3=0;
        Operators.time_solve4=0;
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
        long curTime=0;
        /*if(state.getProperties().toString().equals("true")){

          //  CFAEdge edge = new BlankEdge("loop", loc.getLineNumber(), loc, loc, "loop");
          //  loc.addEnteringEdge(edge);
          //  loc.addLeavingEdge(edge);
          //  state.addParent(state);
          //  state.setForlumas(null);
          //  selfLoop.add(state);

          spu = findCounterexampleSelfLoop(state, reachedSet);

          if (spu == 1) {//发现反例
            reachedSet.add(state, precision);
            Operators.valuesOfkeyVars = state.getModel();
//            if(Operators.valuesOfkeyVars.equals("")){
//              continue;
//            }
            Path pPath = ARGUtils.getOnePathTo(state);
            System.out.println("反例路径为："+pPath.toString());
            List<CFAEdge> edgeList = pPath.asEdgesList();
            ImmutableList<Formula> formulas = from(pPath)
                .transform(Pair.<ARGState> getProjectionToFirst())
                .transform(toState(PredicateAbstractState.class))
                .transform(Operators.GET_BLOCK_FORMULA)
                .toImmutableList();
            int index=1;
            System.out.println(edgeList.size());
            for (CFAEdge e : edgeList) {
              if (e == null||index==edgeList.size()) {
                continue;
              }
              if (e.isKeyEdge()) {
                if (e.isInputEdge()&&!(e instanceof CAssumeEdge)) {//是输入边则保存变量名
                  Formula var = formulas.get(index);//得到公式中对应位置的变量
                  String s1=var.toString();
                  String sVar[] = s1.split("\\|| ");////以竖线(|)或空格分割
                  Operators.valuesOfAllInputVars.add(sVar[1]);
                }
              } else {
                if (e.isInputEdge()) {//是输入边，但不是关键变量，则保存一个随机数
                  Random value = new Random();
                  int x = value.nextInt(100000);//生成一个随机值
                  Operators.valuesOfAllInputVars.add(String.valueOf(x));
                }
              }
              index++;
            }

            Operators.writeValuesOfVars();
            //动态执行检查是否是虚假反例，并在必要时添加关键变量.....
            int oldKeyVarsNum=KeyVar.keyVarSet.size();
            boolean isTrueConterExample = Operators.DynamicExe(pPath);
            System.out.println("动态验证结果:"+isTrueConterExample);
            int newKeyVarsNum=KeyVar.keyVarSet.size();
            if (!isTrueConterExample) {//动态执行发现是假反例时，添加新的关键变量
                System.out.println("发现假反例");
                System.out.println("新的关键变量集合为：" + KeyVar.keyVarSet.toString());
                if(newKeyVarsNum!=oldKeyVarsNum){
                  Operators.markKeyEdgesOfCFA(Operators.cfa);

                  AbstractState root = reachedSet.getFirstState();
                  Precision rootPrecision = reachedSet.getPrecision(root);
                  while (reachedSet.getWaitlistSize() != 0) {
                    reachedSet.popFromWaitlist();
                  }
                  //reachedSet.clear();

                  ArrayList<ARGState> tmpList = new ArrayList<ARGState>(((ARGState) root).getChildren());
                  for (int k = 0; k < tmpList.size(); k++) {
                    ARGState eleState = tmpList.get(k);
                    eleState.removeFromARG();
                  }
                  reachedSet.clear();
                  reachedSet.add(root, rootPrecision);
                  //return CounterexampleInfo.spurious();
                //} catch (IOException e1) {
                  // TODO Auto-generated catch block
                  //e1.printStackTrace();
                //}
              }

            } else {
              spu=1;
              break;
            }
            spu=0;
            continue
            ;
          }

         continue;
        }*/
        for (int j = 0; j < newProperties.size(); j++) {//一个状态只能有一个性质,所以分开操作
          //System.out.println("###########");
          //List<String> curProperties=new ArrayList<>();
          int numSuccessors = 0;
          Transition curProperties = newProperties.get(j);
          List<Integer> curUtil = map.get(curProperties);
          //addLoopCode
          boolean isEqualToBranch = false;
          List<CFAEdge> newEdge = new ArrayList<CFAEdge>();
//          if (loc.getNumLeavingEdges() == 1 && isEqualToBranch(loc)) {
//            isEqualToBranch = true;
//            //换边
//            changeEdges(newEdge, state, loc, proposition);
//          }
//          if (isEqualToBranch) {
//            loc.getLeavingEdge().clear();
//            loc.getLeavingEdge().addAll(newEdge);
//            numSuccessors = 1;
//          }

          Collection<? extends AbstractState> successors =
              transferRelation.getAbstractSuccessors(state, precision, null);
          // TODO When we have a nice way to mark the analysis result as incomplete,
          // we could continue analysis on a CPATransferException with the next state from waitlist.
          numSuccessors = successors.size();
          logger.log(Level.FINER, "Current state has", numSuccessors,
              "successors");
          if (numSuccessors == 1) {
            isTwo = false;
          } else if (numSuccessors == 2) {
            isTwo = true;
          } else {
            //c程序结束,最后一个状态自循环
            if (loc.getNumLeavingEdges() == 0 && !selfLoop.contains(state)) {
              //  CFAEdge edge = new BlankEdge("loop", loc.getLineNumber(), loc, loc, "loop");
              //  loc.addEnteringEdge(edge);
              //  loc.addLeavingEdge(edge);
              //  state.addParent(state);
              //  state.setForlumas(null);
              //  selfLoop.add(state);

              spu = findCounterexampleSelfLoop(state, reachedSet);

              if (spu == 1) {//发现反例
                reachedSet.add(state, precision);
                Operators.valuesOfkeyVars = state.getModel();
                if(Operators.valuesOfkeyVars.equals("")){
                  System.out.println("错误：关键路劲为空");
                }
                Path pPath = ARGUtils.getOnePathTo(state);
                List<CFAEdge> edgeList = pPath.asEdgesList();
                ImmutableList<Formula> formulas = from(pPath)
                    .transform(Pair.<ARGState> getProjectionToFirst())
                    .transform(toState(PredicateAbstractState.class))
                    .transform(Operators.GET_BLOCK_FORMULA)
                    .toImmutableList();
                int index=1;
                System.out.println(edgeList.size());
                for (CFAEdge e : edgeList) {
                  if (e == null||index==edgeList.size()) {
                    continue;
                  }
                  if (e.isKeyEdge()) {
                    if (e.isInputEdge()&&!(e instanceof CAssumeEdge)) {//是输入边则保存变量名
                      Formula var = formulas.get(index);//得到公式中对应位置的变量
                      String s1=var.toString();
                      String sVar[] = s1.split("\\|| ");////以竖线(|)或空格分割
                      Operators.valuesOfAllInputVars.add(sVar[1]);
                    }
                  } else {
                    if (e.isInputEdge()) {//是输入边，但不是关键变量，则保存一个随机数
                      Random value = new Random();
                      int x = value.nextInt(100000);//生成一个随机值
                      Operators.valuesOfAllInputVars.add(String.valueOf(x));
                    }
                  }
                  index++;
                }

                Operators.writeValuesOfVars();
                //动态执行检查是否是虚假反例，并在必要时添加关键变量.....
                int oldKeyVarsNum=KeyVar.keyVarSet.size();
                boolean isTrueConterExample = Operators.DynamicExe(pPath);
                System.out.println("动态验证结果:"+isTrueConterExample);
                int newKeyVarsNum=KeyVar.keyVarSet.size();
                if (!isTrueConterExample) {//动态执行发现是假反例时，添加新的关键变量
                    System.out.println("发现假反例");

                    System.out.println("新的关键变量集合为：" + KeyVar.keyVarSet.toString());
                    if(newKeyVarsNum!=oldKeyVarsNum){
                      Operators.markKeyEdgesOfCFA(Operators.cfa);

                      AbstractState root = reachedSet.getFirstState();
                      Precision rootPrecision = reachedSet.getPrecision(root);
                      while (reachedSet.getWaitlistSize() != 0) {
                        reachedSet.popFromWaitlist();
                      }
                      //reachedSet.clear();

                      ArrayList<ARGState> tmpList = new ArrayList<ARGState>(((ARGState) root).getChildren());
                      for (int k = 0; k < tmpList.size(); k++) {
                        ARGState eleState = tmpList.get(k);
                        eleState.removeFromARG();
                      }
                      reachedSet.clear();
                      reachedSet.add(root, rootPrecision);
                      //return CounterexampleInfo.spurious();
                    //} catch (IOException e1) {
                      // TODO Auto-generated catch block
                      //e1.printStackTrace();
                    //}
                  }

                } else {
                  spu=1;
                  break;
                }
                spu=0;
                break;
              }

            }
            continue;
          }
          //do {
          for (AbstractState successor : Iterables.consumingIterable(successors)) {
            logger.log(Level.FINER, "Considering successor of current state");
            logger.log(Level.ALL, "Successor of", state, "\nis", successor);
            //<yangkai>
            CFANode sucLoc = AbstractStates.extractLocation(successor);
            Operators.tempEdge = loc.getEdgeTo(sucLoc);
            curTime=System.currentTimeMillis();
            Triple<AbstractState, Precision, Action> precAdjustmentResult =
                precisionAdjustment.prec(successor, precision, reachedSet);
            curTime=System.currentTimeMillis()-curTime;
            Operators.time_solve3+=curTime;

            successor = precAdjustmentResult.getFirst();
            Precision successorPrecision = precAdjustmentResult.getSecond();
            Action action = precAdjustmentResult.getThird();

            //调试用


            if (action == Action.BREAK) {
              reachedSet.setResult(Result.SAFE);
              Runtime rt = Runtime.getRuntime();
              System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
              return errorState;

            }
            //((ARGState) successor).copyVarInfos(state.stack);
            ((ARGState) successor).setLevel(level);
            ((ARGState) successor).setProposition(state.getProposition());
            //List<Formula> fft = state.getFormulas();
            ((ARGState) successor).setForlumas(state.getFormulas());
            ((ARGState) successor).setTransition(curProperties);
            ((ARGState) successor).setKeyFormulas(Operators.tempKeyFormulas);
            Operators.time_solve4=System.currentTimeMillis();
            CounterexampleInfo cexInfo =
                mRefiner.performRefinementForProperty(successor, proposition, checkType, isTwo);
            Operators.time_solve4=System.currentTimeMillis()- Operators.time_solve4;
           //yangkai 设置当前状态的可达域
            ((ARGState)successor).setValuesOfKeyVariables(Operators.lastValues);

            if(((ARGState)successor).getStateId()==122121){
               i=i+1-1;
            }


            Operators.lastValues.clear();
            //<yangkai>
            if (Operators.isUnSat) {
              if (Operators.tempKeyFormulas.size() != 0 && Operators.tempEdge.isKeyEdge())
                Operators.tempKeyFormulas.remove(Operators.tempKeyFormulas.size() - 1);
              continue;
            }

            //设置当前节点中input变量的范围,用1和0表示then和else
            if(sucLoc.isLoopStart()){
              ((ARGState)successor).setRangeOfInputVars("");
            }
            else if(Operators.tempEdge.isInputEdge() && Operators.tempEdge.isKeyEdge()&&Operators.tempEdge instanceof CAssumeEdge){
              String s1=state.getRangeOfInputVars();
              String s2=Operators.tempEdge.getDescription();
              ((ARGState)successor).setRangeOfInputVars(s1+"#"+s2);
              /*if(((CAssumeEdge) Operators.tempEdge).getTruthAssumption()){
                 ((ARGState)successor).setRangeOfInputVars(s1+1);
              }
              else
              {
                ((ARGState)successor).setRangeOfInputVars(s1+0);
              }*/

            }
            else{
              String s1=state.getRangeOfInputVars();
              ((ARGState)successor).setRangeOfInputVars(s1);
            }


            if (Operators.tempKeyFormulas.size() != 0 && Operators.tempEdge.isKeyEdge())
              Operators.tempKeyFormulas.remove(Operators.tempKeyFormulas.size() - 1);
            if (((ARGState) successor).getTransition() == null) {
              state.getChildren().remove(successor);
              continue;
            }
            ((ARGState) successor).setProposition(cexInfo.getProposition());
//            if(curProperties.getTarget_state().toString().equals("true")){
//              i=i+1;
//            }
            ((ARGState) successor).setProperties(curProperties.getTarget_state());

            ((ARGState) successor).setUtil(curUtil);

            if(Operators.entryMain&&(sucLoc.getNumLeavingEdges()==0||curProperties.getTarget_state().toString().equals("true"))){
              ((ARGState) successor).setModel(Operators.model.toString());
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
            boolean stop = false;//stopOperator.stop(successor, reached, precision);//cpachecker自身求覆盖,加入新的限制
            stop=Operators.FindCoveredNode(successor, reached);
            if(loc.getNumLeavingEdges()>1){
              ((ARGState)successor).setLastTerms(Operators.lastTerms);
            }
            if (!stop) {
              if(curProperties.getTarget_state().toString().equals("true")){
                Operators.propertyIsTrue=true;
              }
              reachedSet.add(successor, successorPrecision);
              computeFlag(state, (ARGState) successor, curUtil);
              Operators.propertyIsTrue=false;
            }
            else {
              ARGState coveringState = ((ARGState) successor).getCoveringState();
              state.getChildren().add(coveringState);
              coveringState.getParents().add(state);
              computeFlag(state, (ARGState) successor, curUtil);
              //state.getChildren().remove(successor);
              CFANode coverLoc = AbstractStates.extractLocation(coveringState);
              addRelation(loc, AbstractStates.extractLocation(coveringState));
             // if (loopHeadNode.contains(coverLoc)) {

              spu = findCounterexampleCovered((ARGState) successor, state, reachedSet);
              Path pLoopPath = ARGUtils.getOnePathTo(state);
              //System.out.println("循环路径为："+pLoopPath.toString());

              if (spu == 1) {//发现反例
                  reachedSet.add(state, successorPrecision);

                  Operators.valuesOfkeyVars = Operators.model.toString();
                  if(Operators.valuesOfkeyVars.equals("")){
                      System.out.println("：关键路径为空");
                  }
                  Path pPath = ARGUtils.getOnePathTo(state);
                  System.out.println("反例路径为："+pPath.toString());
                  List<CFAEdge> edgeList = pPath.asEdgesList();
                  ImmutableList<Formula> formulas = from(pPath)
                      .transform(Pair.<ARGState> getProjectionToFirst())
                      .transform(toState(PredicateAbstractState.class))
                      .transform(Operators.GET_BLOCK_FORMULA)
                      .toImmutableList();
                  int index=1;
                  for (CFAEdge e : edgeList) {
                    if (index==edgeList.size()) {
                      continue;
                    }
                    if (e.isKeyEdge()) {
                      if (e.isInputEdge()&&!(e instanceof CAssumeEdge)) {//是输入边则保存变量名
                        Formula var = formulas.get(index);//得到公式中对应位置的变量
                        String sVar[] = var.toString().split("\\|| ");//以竖线(|)或空格分割
                        Operators.valuesOfAllInputVars.add(sVar[1]);
                      }
                    } else {
                      if (e.isInputEdge()&&!(e instanceof CAssumeEdge)) {//是输入边，但不是关键变量，则保存一个随机数
                        Random value = new Random();
                        int x = value.nextInt(100000);//生成一个随机值
                        Operators.valuesOfAllInputVars.add(String.valueOf(x));
                      }
                    }
                    index++;
                  }

                  //将输入变量的值写入文件中
                  Operators.writeValuesOfVars();
                  //动态执行并检查并加入新的关键变量.....返回false表示假反例
                  int oldKeyVarsNum=KeyVar.keyVarSet.size();
                  boolean isTrueConterExample = Operators.DynamicExe(pPath);
                  int newKeyVarsNum=KeyVar.keyVarSet.size();
                  System.out.println("动态验证结果:"+isTrueConterExample);
                  //动态执行发现是假反例时，并且发现新的关键变量时，重新展开
                  if (!isTrueConterExample ) {
                    if(oldKeyVarsNum!=newKeyVarsNum){//发现新的关键变量时重新展开
                      System.out.println("发现假反例");
                      System.out.println("新的关键变量集合为：" + KeyVar.keyVarSet.toString());
                      Operators.markKeyEdgesOfCFA(Operators.cfa);

                      AbstractState root = reachedSet.getFirstState();
                      Precision rootPrecision = reachedSet.getPrecision(root);
                      while (reachedSet.getWaitlistSize() != 0) {
                        reachedSet.popFromWaitlist();
                      }
                      //reachedSet.clear();

                      ArrayList<ARGState> tmpList = new ArrayList<ARGState>(((ARGState) root).getChildren());
                      for (int k = 0; k < tmpList.size(); k++) {
                        ARGState eleState = tmpList.get(k);
                        eleState.removeFromARG();
                      }
                      reachedSet.clear();
                      reachedSet.add(root, rootPrecision);
                    }

                      //return CounterexampleInfo.spurious();
                    //} catch (IOException e1) {
                      // TODO Auto-generated catch block
                      //e1.printStackTrace();
                    //}
                  } else {
                    spu=1;
                    break;
                  }
                  spu=0;
                  //break;
                }
             // } //else {
              //  reachedSet.add(successor, successorPrecision);
              //}
            }
            logger.log(Level.FINER,
                "No need to stop, adding successor to waitlist");
          }
          //} while (isEqualToBranch);
        }

        state.setForlumas(null);
        //删除某些节点上保存的输入变量范围以节省内存
        if(loc.getEnteringEdges()!=null && loc.getNumEnteringEdges()==1){
           state.setRangeOfInputVars("");
        }
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
      else{
              reachedSet.setResult(Result.UNSAFE);
              ((ARGState) reachedSet.getLastState()).setMyTarget(true);
              reset();
              //Runtime rt = Runtime.getRuntime();
              //System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
              return errorState;
            }
      //refine call
      //logger.log(Level.FINE, "Error found, performing CEGAR");

//      boolean refinementResult=false;
//      try {
//        refinementResult = mRefiner.performRefinement(reachedSet);//analysis
//      } catch (RefinementFailedException e) {
//        throw e;
//      }
//
//      logger.log(Level.FINE, "Refinement successful:", refinementResult);
//
//      if (refinementResult) {
//        covered.clear();
//        selfLoop.clear();
//        spu = 0;
//      } else {
//        reachedSet.setResult(Result.UNSAFE);
//        ((ARGState) reachedSet.getLastState()).setMyTarget(true);
//        reset();
//        //Runtime rt = Runtime.getRuntime();
//        //System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
//        return errorState;
//      }
      //}while(covered.size()!=0||selfLoop.size()!=0);
    }
    reset();
    //Runtime rt = Runtime.getRuntime();
    //System.out.println("内存1:" + (rt.totalMemory() - rt.freeMemory()));
    return errorState;
  }


  private void changeEdges(List<CFAEdge> pNewEdge, ARGState state, CFANode loc, Proposition proposition) {
    // TODO Auto-generated method stub
    CFAEdge edgeSuc = loc.getLeavingEdge(0);
    assert (edgeSuc instanceof CDeclarationEdge || edgeSuc instanceof CStatementEdge);
    String raw = edgeSuc.getRawStatement();
    String left = raw.substring(0, raw.indexOf("=")).trim();
    if (edgeSuc instanceof CDeclarationEdge)
      left = ((CDeclarationEdge) edgeSuc).getDeclarationVar();
    else if (edgeSuc instanceof CStatementEdge) {
      left = ((CStatementEdge) edgeSuc).getLeft();
    }
    assert (left != null);
    Map<Pair<String, String>, String> propositions = proposition.getPropositions();
    Set<Pair<String, String>> keys = propositions.keySet();
    Iterator<Pair<String, String>> iterator = keys.iterator();
    while (iterator.hasNext()) {
      Pair<String, String> next = iterator.next();
      String second = next.getSecond();//命题
      //String value=propositions.get(next);//函数名
      String funcname = edgeSuc.getPredecessor().getFunctionName();
      String array[] = second.split("([<>=!]+=)|([<>])");
      String function = "";
      String newStatement = "";
      String global = "";
      if (proposition.getGlobalVar().contains(left)) {
        global = "int " + left + ";";
        funcname = "main";
      }
      if (array[0].equals(left)) {
        int i = 0;
        while (i < 2) {
          if (i == 0) {
            if (second.contains("=="))
              newStatement = left + "=" + array[1] + ";";
            else
              newStatement = left + "=" + array[1] + "+1;";
          } else {
            newStatement = left + "=" + array[1] + "-1;";
          }
          i++;
          function = global + "void " + funcname + "(){" + newStatement + "}";
          try {
            ParseResult myString = PropositionInfo.parser.parseString(function);
            Map<String, FunctionEntryNode> fn = myString.getFunctions();
            CFANode node = fn.get(funcname);
            while (node.getNumLeavingEdges() != 0) {
              CFAEdge edge = node.getLeavingEdge(0);
              if (edge.getRawStatement().equals(newStatement)) {
                pNewEdge.add(edge);
                break;
              } else {
                node = edge.getSuccessor();
              }
            }
          } catch (ParserException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
        }
      }
    }
    CFANode pre = edgeSuc.getPredecessor();
    CFANode suc = edgeSuc.getSuccessor();
    CFANode newNode = null;
    for (int i = 0; i < pNewEdge.size(); i++) {
      CFAEdge edge = pNewEdge.get(i);
      if (i == 0) {
        edge.setPredecessor(pre);
        edge.setSuccessor(suc);
        pre.addLeavingEdge(edge);
        suc.addEnteringEdge(edge);
      } else {
        edge.setPredecessor(pre);
        newNode = new CFANode(edgeSuc.getLineNumber(), pre.getFunctionName());
        edge.setSuccessor(newNode);
        newNode.addEnteringEdge(edge);
        BlankEdge blank = new BlankEdge("myBlank", edgeSuc.getLineNumber(), newNode, suc, "");
        newNode.addLeavingEdge(blank);
        pre.addLeavingEdge(edge);
        suc.addEnteringEdge(blank);
      }
    }
    pre.removeLeavingEdge(edgeSuc);
    suc.removeEnteringEdge(edgeSuc);
    if (newNode != null)
      LocationState.LocationStateFactory.initialize1(newNode);
  }

  private boolean isRandomFunctions(String rightString) {
    // TODO Auto-generated method stub
    String array[] = { "nondet_int()", "random()", "int_nondet()", "__VERIFIER_nondet_int()", "nondet()",
        "__VERIFIER_nondet_short()", "__VERIFIER_nondet_char()", "__VERIFIER_nondet_float()" };
    for (int i = 0; i < array.length; i++)
      if (rightString.contains(array[i]))
        return true;
    return false;
  }

  private boolean isEqualToBranch(CFANode pLoc) {
    // TODO Auto-generated method stub
    CFAEdge edgeSuc = pLoc.getLeavingEdge(0);
    String funcname = edgeSuc.getPredecessor().getFunctionName();
    if (edgeSuc instanceof CStatementEdge) {
      CStatement statement = ((CStatementEdge) edgeSuc).getStatement();
      if (statement instanceof CFunctionCallAssignmentStatement) {
        CExpression left = ((CFunctionCallAssignmentStatement) statement).getLeftHandSide();
        CFunctionCallExpression right = ((CFunctionCallAssignmentStatement) statement).getRightHandSide();
        String rightString = right.toASTString();
        String leftString = left.toASTString();
        if (isRandomFunctions(rightString)) {
          if (PropositionInfo.getInstance().getProLeftSide().keySet().contains(leftString)) { return true; }
          if (left instanceof CIdExpression) {
            CSimpleDeclaration dec = ((CIdExpression) left).getDeclaration();
            if (dec instanceof CVariableDeclaration) {
              if (((CVariableDeclaration) dec).isGlobal())
                funcname = "global";
              leftString = funcname + "::" + leftString;
              if (!unknownVars.contains(leftString))
                unknownVars.add(leftString);
            }
          }
        } else {
          if (left instanceof CIdExpression) {
            String lv = ((CIdExpression) left).getName();
            CSimpleDeclaration dec = ((CIdExpression) left).getDeclaration();
            if (dec instanceof CVariableDeclaration) {
              if (((CVariableDeclaration) dec).isGlobal())
                funcname = "global";
            }
            lv = funcname + "::" + lv;
            if (unknownVars.contains(lv)) {
              unknownVars.remove(lv);
            }
          }

        }
      } else if (statement instanceof CExpressionAssignmentStatement) {
        CExpression left = ((CExpressionAssignmentStatement) statement).getLeftHandSide();
        CExpression right = ((CExpressionAssignmentStatement) statement).getRightHandSide();
        String lv = "";
        String leftString = left.toASTString();
        boolean unknown = right.varIsKnown(unknownVars, funcname);
        if (unknown) {
          if (PropositionInfo.getInstance().getProLeftSide().keySet().contains(leftString))
            return true;
        }
        if (left instanceof CIdExpression) {
          lv = ((CIdExpression) left).getName();
          CSimpleDeclaration dec = ((CIdExpression) left).getDeclaration();
          if (dec instanceof CVariableDeclaration) {
            if (((CVariableDeclaration) dec).isGlobal())
              funcname = "global";
          }
          lv = funcname + "::" + lv;
          if (unknown && !unknownVars.contains(lv)) {
            unknownVars.add(lv);
          } else if (!unknown) {
            unknownVars.remove(lv);
          }
        }
      }
    }
    return false;
  }

  private void addRelation(CFANode pre, CFANode suc) {
    //CFAEdge preToSuc=pre.getEdgeTo(suc);
    CFAEdge blankEdge = new BlankEdge("BLANKEDGE", pre.getLineNumber(), pre, suc, "myblank");
    pre.getLeavingEdge().add(blankEdge);
    suc.getEnteringEdges().add(blankEdge);
  }

  private int findCounterexampleCovered(ARGState successor, ARGState state, ReachedSet reached) {

    // covered.remove(state);
    ARGState covering = successor.getCoveringState();
    Set<ARGState> path = ARGUtils.getOnePathToARGStateForSimpleProperty(covering, state);
    if (path == null) { return 0; }
    Set<Integer> utilFlag = new HashSet<Integer>();
    ARGUtils.getUtilFlagForPath(path, utilFlag);
    //Iterator<Integer> itFlag = utilFlag.keySet().iterator();
    boolean isCex = false;
    utilFlag.retainAll(allMy);
    if (utilFlag.size() == allMy.size())
      isCex = true;
    //      boolean isNULL = true;
    //      while (itFlag.hasNext()) {
    //        isNULL = true;
    //        Collection<Integer> next = utilFlag.get(itFlag.next());
    //        if (next.size() == 1)
    //          break;
    //        Iterator<ARGState> iterator = path.getStateSet().iterator();
    //        while (iterator.hasNext()) {
    //          int stateId = iterator.next().getStateId();
    //          if (next.contains(stateId)) {
    //            isNULL = false;
    //            break;
    //          }
    //        }
    //        if (isNULL)
    //          break;
    //      }
    //      isCex = isNULL ? false : true;

    if (isCex) {

      reached.setLastState(state);
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
    } else {
      state.uncover();
      return false;
    }
  }

  private List<Transition> getProperties(AbstractState curState, NFGJni jni) {
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
    } else {
      //NFGJni jni = new NFGJni(curPro); //展开ltl性质
      jni.process(curPro);
      String source = getNFUtilFlag(jni);
      tmpList = jni.get_resutl();
      nf.put(source, tmpList);
    }
    Iterator<Transition> itTmp = tmpList.iterator();
    while (itTmp.hasNext()) { //性质的展开项
      //Set<Transition> newProTemp = new HashSet<Transition>();
      Transition t = itTmp.next();
      String label = t.getLabel(); //性质的当前状态
      label = label.replaceAll("[\\(|\\)| ]", "");
      String target = t.getTarget_state();
      if (target.equals("false")) {
        ((ARGState) curState).setFalse(true);
        continue;
      }
      newPro.add(t);
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
      //System.out.println();
      String target_State = jni.trans__point_string(t);
      String trans_label = jni.state_trans_string(t);
      Transition one = new Transition(trans_label, source_State, target_State);
      if (!hasUnfoldProperty.contains(source)) {
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
