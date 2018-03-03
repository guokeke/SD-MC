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
package org.xidian.cpachecker.dz;

import java.io.BufferedReader;
import java.io.File;
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
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.cpachecker.cfa.CParser;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression.UnaryOperator;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.defaults.AbstractSingleWrapperCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.SimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment.Action;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGSimplePrecisionAdjustment;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.sosy_lab.cpachecker.cpa.predicate.BlockOperator;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionManager;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateRefiner;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.InvalidComponentException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.CachingPathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.ExtendedFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.FormulaManagerFactory;
import org.sosy_lab.cpachecker.util.predicates.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.PathFormulaManagerImpl;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.SymbolicRegionManager;
import org.sosy_lab.cpachecker.util.predicates.bdd.BDDRegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.TheoremProver;
import org.xidian.crl.CRLGlobal;

import com.google.common.base.Throwables;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import com.songstan.ltl_trans.jni.NFGJni;
import com.songstan.ltl_trans.method.Transition;


public class MyCPA extends AbstractSingleWrapperCPA{
  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(PredicateCPA.class).withOptions(BlockOperator.class);
  }

  @Option(name="abstraction.type", toUppercase=true, values={"BDD", "FORMULA"},
      description="What to use for storing abstractions")
  private String abstractionType = "BDD";

  @Option(name="abstraction.initialPredicates",
      description="get an initial set of predicates from a file in MSAT format")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private File predicatesFile = null;

  @Option(description="always check satisfiability at end of block, even if precision is empty")
  private boolean checkBlockFeasibility = false;

  @Option(name="blk.useCache", description="use caching of path formulas")
  private boolean useCache = true;

  @Option(name="enableBlockreducer", description="Enable the possibility to precompute explicit abstraction locations.")
  private boolean enableBlockreducer = false;

  @Option(name="merge", values={"SEP", "ABE"}, toUppercase=true,
      description="which merge operator to use for predicate cpa (usually ABE should be used)")
  private String mergeType = "ABE";

  //private final Configuration config;
  private final LogManager logger;

  public static ExtendedFormulaManager formulaManager;
  private final FormulaManagerFactory formulaManagerFactory;
  public static PathFormulaManager pathFormulaManager=null;
  public static Solver solver;
  private final AbstractionManager abstractionManager;
  public final PredicateAbstractionManager predicateManager;
  private final ConfigurableProgramAnalysis cpa;
  //private final PredicateRefinementManager pRefinementManager;
  private Refiner mRefiner;
  public static  CParser parser;
  @ClassOption(packagePrefix = "org.sosy_lab.cpachecker")
  private Class<? extends Refiner> refiner = PredicateRefiner.class;


 // private final AbstractDomain abstractDomain;
  private final TransferRelation transferRelation;
  //private final MergeOperator mergeOperator;
  //private final StopOperator stopOperator;
  private final PrecisionAdjustment precisionAdjustment;
  //private final Reducer reducer;
  //private final Statistics stats;
  //private final ProofChecker wrappedProofChecker;
  private Map<String,List<Transition>> nf=new HashMap<String,List<Transition>>();
  private Map<String,List<Integer>> map=new HashMap<String,List<Integer>>();
  private int max=0;
  private Set<Integer> used=new HashSet<Integer>();
  private Multimap<Integer,Integer> utilFlag=HashMultimap.create();
  private List<ARGState> covered=new ArrayList<ARGState>();
  private List<ARGState> selfLoop=new ArrayList<ARGState>();
  private List<Integer> allMy=new ArrayList<Integer>();
  private String fs="";

  ///构造函数===========================================================================================构造函数
  public MyCPA(Configuration config, LogManager logger,ConfigurableProgramAnalysis pCpa) throws InvalidConfigurationException, CPAException{
    super(pCpa);
    //this.config = config;
    this.logger = logger;
    this.cpa=pCpa;
    formulaManagerFactory = new FormulaManagerFactory(config, logger);
    //ArithmeticSmtInterpolFormulaManager f=(ArithmeticSmtInterpolFormulaManager) formulaManagerFactory .getFormulaManager();
    formulaManager = new ExtendedFormulaManager(formulaManagerFactory.getFormulaManager(), config, logger);
    PathFormulaManager pfMgr = new PathFormulaManagerImpl(formulaManager, config, logger);
    if (useCache) {
      pfMgr = new CachingPathFormulaManager(pfMgr);
    }
    pathFormulaManager = pfMgr;
    TheoremProver theoremProver = formulaManagerFactory.createTheoremProver();
    solver = new Solver(formulaManager, theoremProver);
    RegionManager regionManager;
    if (abstractionType.equals("FORMULA")) {
      regionManager = new SymbolicRegionManager(formulaManager, solver);
    } else {
      assert abstractionType.equals("BDD");
      regionManager = BDDRegionManager.getInstance(config, logger);
    }
    abstractionManager = new AbstractionManager(regionManager, formulaManager, config, logger);
    predicateManager = new PredicateAbstractionManager(abstractionManager, formulaManager, solver, config, logger);
    //pRefinementManager=new PredicateRefinementManager(formulaManager, pfMgr, solver, abstractionManager, formulaManagerFactory, config, logger);
    mRefiner=createInstance(pCpa);//new PredicateRefiner(config, logger, pCpa, pRefinementManager);
    parser=CParser.Factory.getParser(logger, CParser.Factory.getOptions(config));
    GlobalInfo.getInstance().storeFormulaManager(formulaManager);
    //abstractDomain = new FlatLatticeDomain();
    transferRelation = cpa.getTransferRelation();
    PrecisionAdjustment wrappedPrec = cpa.getPrecisionAdjustment();
    if (wrappedPrec instanceof SimplePrecisionAdjustment) {
      precisionAdjustment = new ARGSimplePrecisionAdjustment((SimplePrecisionAdjustment) wrappedPrec);
    } else {
      precisionAdjustment = cpa.getPrecisionAdjustment();
    }
  /*
    if (cpa instanceof ConfigurableProgramAnalysisWithABM) {
      Reducer wrappedReducer = ((ConfigurableProgramAnalysisWithABM)cpa).getReducer();
      if (wrappedReducer != null) {
        reducer = new ARGReducer(wrappedReducer);
      } else {
        reducer = null;
      }
    } else {
      reducer = null;
    }

    if (cpa instanceof ProofChecker) {
      this.wrappedProofChecker = (ProofChecker)cpa;
    } else {
      this.wrappedProofChecker = null;
    }
 */

    //mergeOperator = cpa.getMergeOperator();
    //stopOperator =cpa.getStopOperator();
   // stats = new ARGStatistics(config, this);
    //printClassName();

  }


  //细化过程========================================================================================refiner
  private Refiner createInstance(ConfigurableProgramAnalysis pCpa) throws CPAException, InvalidConfigurationException {
    //config.inject(this);
    // get factory method
    System.out.println("创建CEGAR");
    Method factoryMethod;
    try {
      factoryMethod = refiner.getMethod("create", ConfigurableProgramAnalysis.class);
    } catch (NoSuchMethodException e) {
      throw new InvalidComponentException(refiner, "Refiner", "No public static method \"create\" with exactly one parameter of type ConfigurableProgramAnalysis.");
    }

    // verify signature
    if (!Modifier.isStatic(factoryMethod.getModifiers())) {
      throw new InvalidComponentException(refiner, "Refiner", "Factory method is not static");
    }

    String exception = Classes.verifyDeclaredExceptions(factoryMethod, CPAException.class, InvalidConfigurationException.class);
    if (exception != null) {
      throw new InvalidComponentException(refiner, "Refiner", "Factory method declares the unsupported checked exception " + exception + ".");
    }

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

    if ((refinerObj == null) || !(refinerObj instanceof Refiner)) {
      throw new InvalidComponentException(refiner, "Refiner", "Factory method did not return a Refiner instance.");
    }

    return (Refiner)refinerObj;
  }

  //PathFormula方法得到==============================================================================得到路径公式
  public PathFormula getParentPathFormula(ARGState state){
     return state.getPathFormula();
  }
  //性质到CFA边转化====================================================================================性质到CFA边转化
  @SuppressWarnings("static-access")
  public static Map<Pair<String,String>,CFAEdge> propositionToCFAEdge(Proposition proposition) throws ParserException{
         Map<Pair<String,String>,String> props=proposition.getPropositions();
         //得到四个d，!d,r,！r
         List<Pair<String,String>> list=new ArrayList<Pair<String,String>>(props.keySet());//内容：[(!r, !(a==a)), (r, a==a), (d, a<=10), (!d, !(a<=10))]
         String global="";
         if(proposition.getGlobalVar().size()!=0){
           for(String s: proposition.getGlobalVar()){
             global=global+"int "+s+";\n";
           }
         }
         String[] statements={"",""};
         //对四个命题进行处理===================================
         //用statements[0]存r与d，用statements[1]存!r!d=====让r与d结合，!r和!d结合=======[blkNum!=0&&blkNum==blkNum&&, !(blkNum==blkNum)&&!(blkNum!=0)&&]
         for(int i=0;i<list.size();i++){
           Pair<String,String> pl=list.get(i);


           if(!pl.getFirst().startsWith("!"))
            statements[0]=statements[0]+pl.getSecond()+"&&";
           else
            statements[1]=statements[1]+pl.getSecond()+"&&";
         }
         Map<Pair<String,String>,CFAEdge> pEdges=new HashMap<Pair<String,String>,CFAEdge>();

         for(int i=0;i<2;i++){
           String statement=statements[i];//statements[0]为：a==a&&B<=10&&
           statement=statement.substring(0,statement.lastIndexOf("&&")).trim();
           String[] ss=statement.split("&&");//i=0时ss得到：[a==a, B<=10]
           for(int j=0;j<ss.length;j++){
           statement=ss[j];//0时为：a==a

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

    return pEdges;
  }
  public static List<Map<Pair<String,String>,CFAEdge>> long_propositionToCFAEdge(Proposition proposition,CFAEdge edge) throws ParserException{
    Map<Pair<String,String>,String> props=proposition.getPropositions();
    String arrSubVal = null;//注意：初试化问题，给下面的secondT=secondT.replaceAll(arrName,String.valueOf(arrSubVal));有关，必须初始化
    String  arrLen=null;
    String arrName = null;
    boolean funFlag=false;
    List<Map<Pair<String,String>,CFAEdge>> dNotDEdges=new ArrayList<Map<Pair<String,String>,CFAEdge>>();
    List<Pair<String,String>>  subToLenNums = new ArrayList<Pair<String,String>>();
    Pair<String,String> subToLenNub;


    //得到选择的数组的     方法名：：数组名     字符串
    FileReader fr;
    String ps="";
    try {
      fr = new FileReader("D:\\property\\propositions.txt");
      assert fr!=null;
      BufferedReader br=new BufferedReader(fr);

      String str;
      while((str=br.readLine())!=null){
          ps=ps+str;
         // System.out.println(ps);
      }
      br.close();
    } catch (FileNotFoundException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    String pss=ps.substring(ps.indexOf("au=>")).trim();
    String funnameToArrname=pss.substring(pss.indexOf("==")+2).trim();
    //找到选择的数组名所对应的数组长度
    String funStrLen=CPAchecker.nameToLen.get(funnameToArrname);
    //得到选中数组的名字
    arrName=funnameToArrname.substring(funnameToArrname.indexOf("::")+2).trim();




    //得到数组名称和下标值=================================================================龙开始
    //通过functionCallEdge得到的=========================2
    if(funStrLen.equals("function_parameter_array")){
      // System.out.println(CRLGlobal.getInstance().getFunLenList());
      int temp=CRLGlobal.getInstance().getFunFlgLen();
      Pair<String,String> arrLens=CRLGlobal.getFunLenList().get(temp-1);
      String firstLenStr=arrLens.getFirst();
      String secondLenStr=arrLens.getSecond();

        if(CRLGlobal.getInstance().getFunFlgLen()>0){
          if(secondLenStr.equals("one_array")){//=========================================================一维数组方法参数处理
          //得到数组长度
          //System.out.println(CRLGlobal.getInstance().getFunFlgLen());
          //System.out.println(CRLGlobal.getInstance().getFunLenList());

        arrLen=  firstLenStr+"+"+CRLGlobal.getLeftfunarrlenList().get(temp-1);
        switch(edge.getEdgeType()){
        case AssumeEdge://待解决========================================================1.AssumeEdge
          CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
          CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
          String assumeedgestr= binaryExp.toASTString();
          ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
          myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
          for(String mysublen:myAllAssuSubLens){
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }

          break;
        case StatementEdge://得到数组下标===============================================2.StatementEdge
          CStatementEdge statementEdge=(CStatementEdge)edge;
          CStatement expression=statementEdge.getStatement();
          if(expression instanceof CAssignment){
            CAssignment assignmentExp=(CAssignment)expression;
            CExpression op1=assignmentExp.getLeftHandSide();
            CRightHandSide op2=  assignmentExp.getRightHandSide();
            String op2str=op2.toASTString();
            String op1str=op1.toASTString();
            String str=op1str+"="+op2str;

            if(op1 instanceof CArraySubscriptExpression){
              /*CIdExpression arrSubExp=(CIdExpression)((CArraySubscriptExpression) op1).getArrayExpression();
               arrSubVal=((CArraySubscriptExpression) op1).getSubscriptExpression().toASTString();
               subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
               ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
               myAllSubLens=getAllArrLens(str,arrName);
               for(String mysublen:myAllSubLens){

                 subToLenNums.add(Pair.of(mysublen,arrLen ));
               }
            }

            else if(op1 instanceof CUnaryExpression){
             UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();
             switch(unaryOperator){
             case STAR:
               CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
             BinaryOperator starOperator=  unaryOperand.getOperator();
             switch(starOperator){
             case PLUS:
             /*String  subVal=  unaryOperand.getOperand2().toASTString();
             arrSubVal="("+subVal+")";
             subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
             myAllSubLens=getAllArrLens(str,arrName);
             for(String mysublen:myAllSubLens){

               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }
             }
            }
           }else{
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
             myAllSubLens=getAllArrLens(op2str,arrName);
             for(String mysublen:myAllSubLens){

               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }
           }


          }//赋值if结束CAssignment
          break;
          default://===========================================================================3.其他语句
            String str= edge.toString();
            ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
            myAllSubLens=getAllArrLens(str,arrName);
            for(String mysublen:myAllSubLens){
              subToLenNums.add(Pair.of(mysublen,arrLen ));
            }
            break;

        }


        }else{//=============================================================================================二维数组参数处理

          //得到数组长度
          //System.out.println(CRLGlobal.getInstance().getFunFlgLen());
          //System.out.println(CRLGlobal.getInstance().getFunLenList());


              List<Pair<String,String>> subtwolens=CFAUtils.subTwoLens;
             String firstfullval= firstLenStr;//得到第一个fulllen
             String secondfullval=secondLenStr;//得到第二个fulllen
             for(Pair<String,String> mysubtwolen:subtwolens){
               String firstsublen=mysubtwolen.getFirst();
               String secondsublen=mysubtwolen.getSecond();
               subToLenNums.add(Pair.of(firstsublen, firstfullval));
               subToLenNums.add(Pair.of(secondsublen, secondfullval));
             }
            }






        }



    }//结束第一个if
    else if(funStrLen.equals("pointer_array")){
      arrLen=CRLGlobal.getInstance().getPointerArrFullLen();//得到当前长度
     String tempArrSubVal= CRLGlobal.getInstance().getPointerGloLen();//得到下标临时长度，即上面p的值
     switch(edge.getEdgeType()){
     case AssumeEdge:
       CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
       CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
       String assumeedgestr= binaryExp.toASTString();
       ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
       myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
       for(String mysublen:myAllAssuSubLens){
         mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
         subToLenNums.add(Pair.of(mysublen,arrLen ));
       }
       break;
     case StatementEdge:
       CStatementEdge statementEdge=(CStatementEdge)edge;
       CStatement expression=statementEdge.getStatement();
       if(expression instanceof CAssignment){
         CAssignment assignmentExp=(CAssignment)expression;
         CExpression op1=assignmentExp.getLeftHandSide();
        CRightHandSide op2=  assignmentExp.getRightHandSide();
        String op2str=op2.toASTString();
        String op1str=op1.toASTString();
        String str=op1str+"="+op2str;
        if(op1 instanceof CUnaryExpression){//======================================================左边是*(a+1)形式
          UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();

          switch(unaryOperator){
          case STAR:
            if(((CUnaryExpression) op1).getOperand() instanceof CBinaryExpression){
            CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
          BinaryOperator starOperator=  unaryOperand.getOperator();
          switch(starOperator){
          case PLUS:
          String  subVal=  unaryOperand.getOperand2().toASTString();
          arrLen= CRLGlobal.getInstance().getPointerArrFullLen();

         /* arrSubVal="("+tempArrSubVal+")+"+"("+subVal+")";//得到数组下标，用p临时值加上*(p+1)后面的1
          subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
          ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
          myAllSubLens=getAllArrLens(str,arrName);
          for(String mysublen:myAllSubLens){
            mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }
          }

          }//二元操作结束
            else if(((CUnaryExpression) op1).getOperand() instanceof CIdExpression){
              //CIdExpression unaryOperand=(CIdExpression) ((CUnaryExpression) op1).getOperand();
              /*arrSubVal="("+tempArrSubVal+")";
             arrLen= CRLGlobal.getInstance().getPointerArrFullLen();
              subToLenNums.add(Pair.of(arrSubVal,arrLen));*/
              ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
              myAllSubLens=getAllArrLens(str,arrName);
              for(String mysublen:myAllSubLens){
                mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
                subToLenNums.add(Pair.of(mysublen,arrLen ));
              }


            }
          }
         }//if结束，左边是*()形式结束
        else{
          //注意此处等有*多提取方法再做处理=============================================多方法再处理=====记得注意啊
          ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen======================注意等有了提取所有*()+*()方法时再加入
          myAllSubLens=getAllArrLens(str,arrName);
          for(String mysublen:myAllSubLens){
            mysublen="("+tempArrSubVal+")+"+"("+mysublen+")";
            subToLenNums.add(Pair.of(mysublen,arrLen ));
          }
        }
        }
       break;

     }

    } else if(funStrLen.equals("two_array")){
      List<Pair<String,String>> subtwolens=CFAUtils.subTwoLens;
      Map<String,Pair<String,String>> fulltwolens=CPAchecker.twoLens;
      for(Map.Entry<String,Pair<String,String>> entry:fulltwolens.entrySet()){//遍历map找到fulllength两个
        String key=entry.getKey();
        Pair<String,String> fullvals=entry.getValue();

        if(key.equals(funnameToArrname)){
         String firstfullval= fullvals.getFirst();//得到第一个fulllen
         String secondfullval=fullvals.getSecond();//得到第二个fulllen
         for(Pair<String,String> mysubtwolen:subtwolens){
           String firstsublen=mysubtwolen.getFirst();
           String secondsublen=mysubtwolen.getSecond();
           subToLenNums.add(Pair.of(firstsublen, firstfullval));
           subToLenNums.add(Pair.of(secondsublen, secondfullval));
         }
        }
      }
    }
    //不是通过functionCallEdge得到的=========================1
    else{
      arrLen=funStrLen;   //得到数组长度
      switch(edge.getEdgeType()){
      case AssumeEdge://待解决
        CAssumeEdge assumeEdge = (CAssumeEdge) edge; //[explicit算法中，successor返回null代表不选择该路径分支]
        CBinaryExpression binaryExp=(CBinaryExpression)assumeEdge.getExpression();
        String assumeedgestr= binaryExp.toASTString();
        ArrayList<String> myAllAssuSubLens=new ArrayList<String>();//加入所有sublen
        myAllAssuSubLens=getAllArrLens(assumeedgestr,arrName);
        for(String mysublen:myAllAssuSubLens){
          subToLenNums.add(Pair.of(mysublen,arrLen ));
        }
      break;


      case StatementEdge://得到数组下标
        CStatementEdge statementEdge=(CStatementEdge)edge;
        CStatement expression=statementEdge.getStatement();
        if(expression instanceof CAssignment){
          CAssignment assignmentExp=(CAssignment)expression;
          CExpression op1=assignmentExp.getLeftHandSide();
         CRightHandSide op2=  assignmentExp.getRightHandSide();
         String op2str=op2.toASTString();
         String op1str=op1.toASTString();
         String str=op1str+"="+op2str;
          if(op1 instanceof CArraySubscriptExpression){//===================================================左边是a[]形式
           // CIdExpression arrSubExp=(CIdExpression)((CArraySubscriptExpression) op1).getArrayExpression();
             //arrSubVal=((CArraySubscriptExpression) op1).getSubscriptExpression().toASTString();
             //subToLenNums.add(Pair.of(arrSubVal,arrLen ));
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
             myAllSubLens=getAllArrLens(str,arrName);
             for(String mysublen:myAllSubLens){
               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }



          }else if(op1 instanceof CUnaryExpression){//======================================================左边是*(a+1)形式
            UnaryOperator  unaryOperator=((CUnaryExpression) op1).getOperator();

            switch(unaryOperator){
            case STAR:
              CBinaryExpression unaryOperand=(CBinaryExpression) ((CUnaryExpression) op1).getOperand();
            BinaryOperator starOperator=  unaryOperand.getOperator();
            switch(starOperator){
            case PLUS:
            /*String  subVal=  unaryOperand.getOperand2().toASTString();
            arrSubVal="("+subVal+")";
            subToLenNums.add(Pair.of(arrSubVal,arrLen ));*/
            ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
            myAllSubLens=getAllArrLens(str,arrName);
            for(String mysublen:myAllSubLens){
              subToLenNums.add(Pair.of(mysublen,arrLen ));
            }
            }

            }
           }else{//=====================================================================================左边不是上面的两种形式
             //记得改回来
             ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
             myAllSubLens=getAllArrLens(op2str,arrName);
             for(String mysublen:myAllSubLens){
               subToLenNums.add(Pair.of(mysublen,arrLen ));
             }

           }


        }
        break;

      default:
       String str= edge.getRawStatement();
       ArrayList<String> myAllSubLens=new ArrayList<String>();//加入所有sublen
       myAllSubLens=getAllArrLens(str,arrName);
       for(String mysublen:myAllSubLens){
         subToLenNums.add(Pair.of(mysublen,arrLen ));
       }
       break;
      }

      }


    //龙结束==========================================================================================================龙得到subs和名字和长度结束


    //得到四个d，!d,r,！r
    System.out.println(subToLenNums);

    List<Pair<String,String>> savelist=new ArrayList<Pair<String,String>>(props.keySet());

    String global="";
    if(proposition.getGlobalVar().size()!=0){
      for(String s: proposition.getGlobalVar()){
        global=global+"int "+s+";\n";
      }
    }

    //对四个命题进行处理===================================
    //用statements[0]存r与d，用statements[1]存!r!d=====让r与d结合，!r和!d结合=======[blkNum!=0&&blkNum==blkNum&&, !(blkNum==blkNum)&&!(blkNum!=0)&&]





    for(Pair<String,String> mypl:subToLenNums){//为实现多边一起加入而加入的for循环==============================多边
      List<Pair<String,String>> list=new ArrayList<Pair<String,String>>(savelist);
      String[] statements={"",""};

    for(int i=0;i<list.size();i++){
      //龙测试
      Pair<String,String> pl=list.get(i);
      String firstT=pl.getFirst();//第一个：!r====第二个：r=====第三个：d

      if(pl.getFirst().equals("al")||pl.getFirst().equals("!al")){

        String secondT=pl.getSecond();

            if((secondT!=null)&&(arrName!=null)&&(mypl.getFirst()!=null)&&(mypl.getSecond()!=null)){


                 String   temparrname=arrName.replaceAll("\\*", "\\\\*");
                 temparrname=temparrname.replaceAll("\\.", "\\\\.");
              secondT=secondT.replaceFirst(temparrname,mypl.getFirst());
               secondT=secondT.replaceAll("length",mypl.getSecond());

         }
       pl=Pair.of(firstT,secondT);
       list.set(i, pl);
      }
      //龙测试结束

      if(!pl.getFirst().startsWith("!"))
       statements[0]=statements[0]+pl.getSecond()+"&&";
      else
       statements[1]=statements[1]+pl.getSecond()+"&&";
    }

    Map<Pair<String,String>,CFAEdge> pEdges=new HashMap<Pair<String,String>,CFAEdge>();

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
dNotDEdges.add(pEdges);

    }//加入的for循环结束


return dNotDEdges;
}

  //run1方法=============================================================run1方法  proposition To  CFAEdge
  public static void run1(ReachedSet reachedSet,Proposition proposition) throws ParserException, CPATransferException{
    //把d与!d转化成边============={(d, blkNum!=0)=Line 1: N666 -{[blkNum != 0]}-> N668, (!d, !(blkNum!=0))=Line 1:  N681 -{[!(blkNum != 0)]}-> N683}
    Map<Pair<String,String>,CFAEdge> pEdges=propositionToCFAEdge(proposition);
    proposition.setPropEdges(pEdges);
  }

//run2方法=============================================================run2方法  proposition To  CFAEdge
  public static  List<Proposition> run2(Proposition proposition,CFAEdge rEdge) throws ParserException, CPATransferException{
    //把d与!d转化成边============={(d, blkNum!=0)=Line 1: N666 -{[blkNum != 0]}-> N668, (!d, !(blkNum!=0))=Line 1:  N681 -{[!(blkNum != 0)]}-> N683}
    List<Map<Pair<String,String>,CFAEdge>> pEdges=long_propositionToCFAEdge(proposition,rEdge);
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


  //==run方法============================================================run方法
  public Pair<ARGState, ARGState> run(final ReachedSet reachedSet,Proposition proposition) throws InterruptedException, CPAException, IOException{

    //mycode
    //mycode end
    //final TransferRelation transferRelation = cpa.getTransferRelation();
    //final MergeOperator mergeOperator = cpa.getMergeOperator();
    //final StopOperator stopOperator = cpa.getStopOperator();
    //final PrecisionAdjustment precisionAdjustment =
    //    cpa.getPrecisionAdjustment();
    int level=0;//标记,用来求覆盖
    int i = 0;
    Pair<ARGState,ARGState> errorState=null;//if UNSAFE then the first ARGState whose property is true//加入错误标签
    boolean isTwo=true;//判断后继个数是否为2
    boolean firstB=true;
    map.put("true",new ArrayList<Integer>());
    Proposition non=proposition.negative();
    AbstractState first=reachedSet.getFirstState();
    //把性质读进到ps中!([](r->d))
    FileReader fr=new FileReader("D:\\property\\properties.txt");
    assert fr!=null;
    BufferedReader br=new BufferedReader(fr);
    String ps="";
    String s;
    while((s=br.readLine())!=null){
        ps=ps+s;
    }
    br.close();
    ((ARGState)first).setProperties(ps);
    ((ARGState)first).setProposition(non);



    //对所有节点进行分析找后继分析===================================================================================分析
    while (reachedSet.hasWaitingState()) {
      i = i + 1;
     // if (i % 1000 == 0) {
     //   System.gc();
    //    System.runFinalization();
     // }
      System.out.println(i+","+reachedSet.size());
      //System.out.println("level="+level);
      CPAchecker.stopIfNecessary();
      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration
      //int size = reachedSet.getWaitlistSize();
      final AbstractState state = reachedSet.popFromWaitlist();
      final Precision precision = reachedSet.getPrecision(state);
      level=((ARGState)state).getLevel();
      CFANode loc=AbstractStates.extractLocation(state);

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
         MyCPA.run1(reachedSet, proposition);

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






      //遇到循环分支时判断覆盖================================================================================mystop用到====1
      boolean mystop=false;
      if(loc.isLoopStart()){//遇到循环分支时，判断覆盖
        Collection<AbstractState> reached = reachedSet.getReached(state);
        mystop=mystop((ARGState) state,reached);
      }
      if(mystop){
        //level--;
        continue;
      }


      //((ARGState)state).setCFANode();
      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);

      //得到新性质======================================================================================newProperties=====2
      List<String> newProperties=getProperties(state);//展开性质,并计算下一个状态可以满足的性质
      if(newProperties==null||newProperties.size()==0){
        ((ARGState)state).setFalse(true);
        continue;
      }

      //如果是第一个点=================================================================================进行处理第一个点====3
      if(firstB){
        ((ARGState)state).setUtil(map.get(fs));
        firstB=false;
      }



      //分析性质，如(true U (! (d )&&r))，=================================================性质分开操作，性质点for开始=====4
      for(int j=0;j<newProperties.size();j++){//一个状态只能有一个性质,所以分开操作
        //List<String> curProperties=new ArrayList<>();
       String curProperties=newProperties.get(j);
       List<Integer> curUtil=map.get(curProperties);

         //计算后继========================================================================================计算后继001
       Collection<? extends AbstractState> successors =
          transferRelation.getAbstractSuccessors(state, precision, null);
      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.
      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");


      //设置isTwo，看后继有几个，看是否是两个=======================isTwo==========================================002
      if(numSuccessors==1){
        isTwo=false;
      } else if(numSuccessors==2){
        isTwo=true;
      }else{
        //c程序结束,最后一个状态自循环
        if(!selfLoop.contains(state)){
          CFAEdge edge=new BlankEdge("loop", loc.getLineNumber(), loc, loc,"loop");
          loc.addEnteringEdge(edge);
          loc.addLeavingEdge(edge);
          ((ARGState)state).addParent((ARGState) state);
          ((ARGState)state).setForlumas(null);
          selfLoop.add((ARGState) state);
        }
        continue;
      // }
      /*  else{
          ((ARGState)state).setTarget(true);
          //reachedSet.setResult(Result.UNSAFE);
          reachedSet.setNoSuc(state);
          end=true;
        }*/
      }


      //看是否是loopStart===================================================================================================003
      if(loc.isLoopStart()){
        level++;
        loc.setLevel(level);
        ((ARGState)state).setLevel(level);
      }


      //进行for循环小的===========================================================================小for循环，对successor分析====for开始
      for (AbstractState successor : Iterables.consumingIterable(successors)) {
        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);

        //preAdjustment操作=====================================================================preAdjustment===========004
        Triple<AbstractState, Precision, Action> precAdjustmentResult =
            precisionAdjustment.prec(successor, precision, reachedSet);
        successor = precAdjustmentResult.getFirst();
        Precision successorPrecision = precAdjustmentResult.getSecond();
        //Action action = precAdjustmentResult.getThird();
        ((ARGState)successor).setLevel(level);
        //System.out.println("successor=>"+successor);

        //设置proposition，得到父formulas======把父亲的proposition，和formulas给succesor===========setProposition，setFormulas===005
        ((ARGState)successor).setProposition(((ARGState)state).getProposition());
        reachedSet.add(successor, successorPrecision);
        ((ARGState)successor).setForlumas(((ARGState)state).getFormulas());


        //细化过程=======================细化中加入了proposition==================================细化找到反例过程==========006
        CounterexampleInfo cexInfo=null;//mRefiner.performRefinement1(successor,proposition,isTwo);



        //看反例路径是否是假的===================================================如果是假的，则删除相应东西，继续下个状态======007
        if(cexInfo.isSpurious()&&isTwo){
          //((ARGState)successor).setFalse(true);
          reachedSet.remove(successor);
          ((ARGState)state).getChildren().remove(successor);
          ((ARGState)successor).getParents().remove(state);
          continue;
        }

        //统一设置相应的proposition   properties       Util==============================================================008
        ((ARGState)successor).setProposition(cexInfo.getProposition());
        ((ARGState)successor).setProperties(curProperties);
        ((ARGState)successor).setUtil(curUtil);
        if(curProperties.equals("true")&&errorState==null){//===========================================2
          errorState=Pair.of((ARGState) state,(ARGState) successor);
        }
        computeFlag((ARGState) state,(ARGState) successor,curUtil);


        /*boolean tmp=(((AbstractSingleWrapperState)((ARGState)state).getWrappedState())).getTerminal();
        if(!isTwo&&tmp){
          Collection<AbstractState> reached = reachedSet.getReached();
          ((ARGState)state).setTerminal(tmp);
          mystop1((ARGState) successor,reached);
        }*/
       // assert action == Action.CONTINUE : "Enum Action has unhandled values!";
        //Collection<AbstractState> reached = reachedSet.getReached(successor);
        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
       /* if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
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
       // boolean stop =false;//stopOperator.stop(successor, reached, successorPrecision);


       /* if (stop) {
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");


        } else {*/
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");
          numSuccessors--;
          //if(AbstractStates.extractLocation(successor).isLoopStart())
          //  level++;
          //reachedSet.add(successor, successorPrecision);

        //}
      }//结束for小循环 ================================================================================================for结束

      //System.out.println((state));
      //CFANode locState=AbstractStates.extractLocation(state);

      //设置unKnown===================================================================================================009
      if(loc.isLoopStart()){
        if(numSuccessors==0||loc.getNumLeavingEdges()==1){
          ((ARGState)state).setUnknown(true);
        }else{
          loc.setLevel(loc.getLevel()+1);
        }
       // loc.setUnknown(true);
      }

    }//结束大for，即性质循环=============================================================================================性质for循环结束

      ((ARGState)state).setForlumas(null);
     /* if(!((ARGState)state).isUnknown()||!((ARGState)state).getProperties().equals("true")){
        ((ARGState)state).removeFromARG();
        reachedSet.remove(state);
      }*/
    }//结束while循环======================================================================================================结束while循环

    reset();
    findCounterexample(reachedSet);
    return errorState;
  }//结束run============================================================================================================结束run


 //方法 findCounterexample==========================================================找反例路径方法
  private int findCounterexample(ReachedSet reached) {
    // TODO Auto-generated method stub
    int sum=0;
    boolean hasSet=false;
    if(utilFlag.keySet().size()==0){
     return 0;
    }
    for(ARGState state:selfLoop){
      sum++;
      boolean result=true;
      int stateId=state.getStateId();

      Iterator<Integer> iterator=utilFlag.keySet().iterator();

      while(iterator.hasNext()){
        Collection<Integer> next=utilFlag.get(iterator.next());//每一个标记F所包含的状态ID
        if(next.size()==1){
          result=false;
          break;
        }
        if(!next.contains(stateId)){
          result=false;
          break;
        }
      }
      if(result){
        if(!hasSet){
         reached.setResult(Result.UNSAFE);
         hasSet=true;
        }
          Iterator<ARGState> it=ARGUtils.getOnePathTo(state).getStateSet().iterator();
          while(it.hasNext()){
            it.next().setMyTarget(true);
          }
        state.setMyTarget(true);
      }
    }
    selfLoop=null;
    //Set<Pair<ARGState, ARGState>> highlightedEdges=new HashSet<>();
    for(ARGState state:covered){
      sum++;
      ARGState covering=state.getCoveringState();
      Path path=ARGUtils.getOnePathToARGState(state,covering);
      if(path==null)
        continue;
      Iterator<Integer> itFlag=utilFlag.keySet().iterator();
      boolean isCex=true;
      boolean isNULL=true;
      while(itFlag.hasNext()){
        isNULL=true;
        Collection<Integer> next=utilFlag.get(itFlag.next());
        if(next.size()==1)
          break;
          Iterator<ARGState> iterator=path.getStateSet().iterator();
          while(iterator.hasNext()){
            int stateId=iterator.next().getStateId();
            if(next.contains(stateId)){
              isNULL=false;
              break;
            }
          }
        if(isNULL)
          break;
      }
      isCex=isNULL?false:true;
      if(isCex){
        if(!hasSet){
          reached.setResult(Result.UNSAFE);
          hasSet=true;
         }
        Iterator<ARGState> iterator=ARGUtils.getOnePathTo(state).getStateSet().iterator();
        while(iterator.hasNext()){
          iterator.next().setMyTarget(true);
        }
      }
    }
    System.out.println("sum="+sum);
    return 0;
  }

  //方法reset方法================================================================重置为空方法
  private void reset() {
    // TODO Auto-generated method stub
    map=null;
    used=null;
    nf=null;
  }
  //方法computeFlag方法================================================================计算标记方法
  private void computeFlag(ARGState curState, ARGState successor, List<Integer> util) {
    // TODO Auto-generated method stub
     List<Integer> curFlag=new ArrayList<Integer>();
     for(Integer integer:allMy){
       if(!util.contains(integer)){
         curFlag.add(integer);
         utilFlag.put(integer,successor.getStateId());
       }
     }
     successor.setFlag(curFlag);
  }

  //mystop放法============================================================================看什么时候停止方法mystop
  private boolean mystop(ARGState state, Collection<AbstractState> reached) {
    // TODO Auto-generated method stub
    //boolean result=false;
    Proposition sucP=state.getProposition();
    String sucProperty=state.getProperties();
    Map<Pair<String,String>,String> sucPros=sucP.getPropositions();
    Set<Pair<String,String>> sucSet=sucPros.keySet();
    Iterator<AbstractState> it=reached.iterator();
    while(it.hasNext()){
      ARGState itNext=(ARGState) it.next();
      Set<Pair<String,String>> set=itNext.getProposition().getPropositions().keySet();
      String setProperty=itNext.getProperties();
      CFANode staLoc=AbstractStates.extractLocation(state);
      CFANode itNextLoc=AbstractStates.extractLocation(itNext);
      if(state.getStateId()!=itNext.getStateId()&&itNextLoc.getLevel()==staLoc.getLevel()
          &&set.equals(sucSet)&&sucProperty.equals(setProperty)&&itNext.isUnknown()&&
          !itNext.isCovered()
          ){
        state.setCovered(itNext);
        state.getChildren().clear();
        covered.add(state);
        //itNext.setUnknown(false);
        return true;
      }
    }
    return false;
  }
//getProperties方法=====================================================================得到性质方法
  private List<String> getProperties(AbstractState curState) {
    // TODO Auto-generated method stub
    //boolean bool=true;
    String curPro=((ARGState)curState).getProperties();//范式
    List<String> newPro=new ArrayList<String>();
    //List<Integer> util=new ArrayList<>();
    if(curPro.equals("true")){
      newPro.add(curPro);
      return newPro;
    }
    Set<Pair<String,String>> curPropositions=((ARGState)curState).getProposition().getPropositions().keySet();//命题
    Set<Transition> tmpSet=new HashSet<Transition>();
    if(nf.keySet().contains(curPro)){
      tmpSet.addAll(nf.get(curPro));
    }
    else{
      //property=property.replaceAll("\\w","\\w " );
      //System.out.println(property);
      //property=property.replaceAll(" ","");
      //property=property.replaceAll("true", "T");
     //property=property.replaceAll("false", "F");
      //property=appendSpace(property);
      //property=property.replaceAll("T", "true");
      //property=property.replaceAll("F", "false");
     // System.out.println(curPro);
      NFGJni jni=new NFGJni(curPro);         //展开ltl性质
      tmpSet.addAll(jni.get_resutl());
      getNFUtilFlag(jni);
      nf.put(curPro,new ArrayList<Transition>(tmpSet));

    }
    //System.out.println("tmpset="+tmpSet);
    Iterator<Transition> itTmp=tmpSet.iterator();
    //Set<String> removed=new HashSet<>();
    while(itTmp.hasNext()){      //性质的展开项            //求交集:将ARG的当前状态满足的命题与性质的当前状态求交
      Transition t=itTmp.next();
      //String source=t.getSource_state();
      String label=t.getLabel(); //性质的当前状态
      label=label.replaceAll("[\\(|\\)| ]","");
      String target=t.getTarget_state();
      Iterator<Pair<String,String>> it=curPropositions.iterator();
      while(it.hasNext()){       //ARGState满足的命题
        String prop=it.next().getFirst();
        boolean isTrue=intersection(prop,label);//求交
        if(isTrue){
          if(target.equals("false")){
            ((ARGState)curState).setFalse(true);
            return null;
          }
          else if(!newPro.contains(target)){
            newPro.add(target);
          }
        }
        else{
          if(newPro.contains(target))
            newPro.remove(target);
          break;
        }
      }

    }
    return newPro;
  }
  /*
   * 计算U(util)标记===================================================================计算util方法
   */
  private void getNFUtilFlag(NFGJni jni) {
    // TODO Auto-generated method stub
    boolean f=true;
    Set<Transition> result=null;jni.get_resutl();
    List<Integer> all=new ArrayList<Integer>();
    Map<String,List<Integer>> tmpMap=new HashMap<String,List<Integer>>();
    Map<String,List<Integer>> tmpMap1=new HashMap<String,List<Integer>>();
    long head = jni.nfg_states_head();
    long tail = jni.nfg_states_tail();
    long state=jni.nfg_stateNxt(head);
   // for(long state=jni.nfg_stateNxt(head);state!=tail;state=jni.nfg_stateNxt(state)){
      String source_State = jni.state_string(state);
      if(f){
        fs=source_State;
        f=false;
      }
    long fin1 = jni.get_all_final();
    //System.out.println("all the trans' final is");
    for(int j=0;j<32;j++){
      if((fin1&(1<<j))>0){
        //System.out.print(j+" ");
        all.add(j);
        if(!utilFlag.keySet().contains(j))
          utilFlag.put(j,null);
      }
    }
    if(allMy.size()==0){
      allMy.addAll(all);
    }
     // System.out.println("\n"+source_State);
      long trans = jni.nfg_stateFirstTrans(state);
      for(long t = jni.nfg_transNxt(trans);t!=trans;t=jni.nfg_transNxt(t)){
        long fin = jni.trans_final(t);
       // System.out.println("the trans' final is");
        List<Integer> tmp=new ArrayList<Integer>(all);
        for(int i=0;i<32;i++){
          if((fin&(1<<i))>0){
           // System.out.print(i+" ");
            tmp.remove(new Integer(i));
          }
        }
        System.out.println();
        String target_State = jni.trans__point_string(t);
        String trans_label = jni.state_trans_string(t);
        tmpMap.put(target_State,tmp);
        Transition one = new Transition(trans_label,source_State,target_State);
        result.add(one);
        //System.out.println(one);
        //System.out.println("......one time ....");
      }
    //}
    Iterator<String> itKeyMap=tmpMap.keySet().iterator();
    Map<Integer,Integer> tmp=new HashMap<Integer,Integer>();
    while(itKeyMap.hasNext()){
      String next=itKeyMap.next();
      List<Integer> nv=tmpMap.get(next);
      if(nv.size()==1){
        int nv0=nv.get(0);
        if(!map.keySet().contains(next)){
          max=max<nv0?nv0:max;
          if(used.contains(nv0)){
            nv.set(0, ++max);
          }
          map.put(next, nv);
        }
        else{
          tmp.put(nv0,map.get(next).get(0));
          tmpMap.put(next,map.get(next));
        }
      }
      else if(nv.size()==0){
        if(!map.keySet().contains(next)){
          map.put(next, nv);
        }
      }
    }
    itKeyMap=tmpMap.keySet().iterator();
    Set<Integer> tmpSet=tmp.keySet();
    while(itKeyMap.hasNext()){
      String next=itKeyMap.next();
      List<Integer> nv=tmpMap.get(next);
      if(nv.size()>1){
         for(int i=0;i<nv.size();i++){
           Integer integer=nv.get(i);
           if(tmpSet.contains(integer)){
             nv.set(i,tmp.get(integer));
           }
         }
         if(!map.keySet().contains(next)){
           map.put(next, nv);
         }
      }
    }

  }
  private final boolean intersection(String p, String q) {
    String array[]=q.split("&&");
    for(int i=0;i<array.length;++i){
      String s=array[i];
      if(s.equals("!"+p)||p.equals("!"+s))
        return false;
    }
    return true;
  }
  public String appendSpace(String  para){
    int length = para.length();
    char[] value = new char[length << 1];
    for (int i=0, j=0; i<length; ++i,j++) {
        value[j] = para.charAt(i);
        if(!isOK(para.charAt(i))){
         value[1+j]=' ';
         j++;
        }
    }
    return new String(value);
}
  private boolean isOK(char ch) {
    // TODO Auto-generated method stub
    if(String.valueOf(ch).matches("[<|\\[|\\-|\\||&|a-z|!]")){
     return true;
    }
    return false;
  }
  @Override
  public AbstractDomain getAbstractDomain() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public TransferRelation getTransferRelation() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public MergeOperator getMergeOperator() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public StopOperator getStopOperator() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public PrecisionAdjustment getPrecisionAdjustment() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public AbstractState getInitialState(CFANode pNode) {
    // TODO Auto-generated method stub
    return null;
  }

  public static ArrayList<String> getAllArrLens(String str,String arrayName){

    Stack<Character>  stack=new Stack<Character>();
    Map<Integer,Integer> map=new HashMap<Integer,Integer>();
    ArrayList<String>  myAllSubs=new ArrayList<String>();
    List<Integer>  templeft=new ArrayList<Integer>();//储存'['的在字符串中位置
    List<Integer>  templeft1=new ArrayList<Integer>();//储存'('的在字符串中位置
    stack.push('A');
        str=str.replaceAll(" ", "");
        if(arrayName.contains(".")){
          arrayName=arrayName.replaceAll(arrayName, "("+arrayName+")");
          arrayName=arrayName.replaceAll("\\(","\\\\(");
          arrayName=arrayName.replaceAll("\\)","\\\\)");
          arrayName=arrayName.replaceAll("\\[","\\\\[");
          arrayName=arrayName.replaceAll("\\]","\\\\]");


          str=str.replaceAll(arrayName, "#");
          }else{ str=str.replaceAll(arrayName, "#");}
        if(str.contains("*#")){
          str=str.replaceAll("\\*\\#", "\\$");
        }
        if(str.contains("*(#)")){
           str= str.replaceAll("\\*\\(\\#\\)", "\\$");
        }
       char[] arr=str.toCharArray();


       for(int k=0;k<arr.length;k++){
         char c=arr[k];
         Character temp =stack.pop();
         if(c=='$'){
           myAllSubs.add("0");
         }
         if(temp=='A'){
           stack.push(temp);
         }



         if (temp == '[' && c == ']') { // ===============================总1

  if((templeft.get(templeft.size()-1)-3)>=0){
    if((arr[templeft.get(templeft.size()-1)-1]=='#')||((arr[templeft.get(templeft.size()-1)-1]==')')&&(arr[templeft.get(templeft.size()-1)-2]=='#')&&(arr[templeft.get(templeft.size()-1)-3]=='('))){

      map.put(templeft.get(templeft.size()-1), k);
      templeft.remove(templeft.size()-1);

      }
  }else{
    if((arr[templeft.get(templeft.size()-1)-1]=='#')){
      map.put(templeft.get(templeft.size()-1), k);
      templeft.remove(templeft.size()-1);
    }
  }





        }else if(temp == '(' && c == ')'){
          if(templeft1.get(templeft1.size()-1)>=1){//考虑 ()左括号前面没东西
            //System.out.println(arr[templeft1.get(templeft1.size()-1)-1]);
            //System.out.println(arr[templeft1.get(templeft1.size()-1)+1]);
          if((arr[templeft1.get(templeft1.size()-1)-1]=='*')&&(arr[templeft1.get(templeft1.size()-1)+1]=='#')){

             map.put(templeft1.get(templeft1.size()-1)+2, k);

             }
             templeft1.remove(templeft1.size()-1);
          }

        }else if(temp=='['||temp=='(')
          stack.push(temp);
         if (c == '[') {
             stack.push(c);
             templeft.add(k);



           } if(c=='('){
             stack.push(c);
             templeft1.add(k);
           }



        }
       for(Map.Entry<Integer,Integer> entry:map.entrySet()){
         int i=entry.getKey();
         int j=entry.getValue();
         String sunstr="("+(String) str.subSequence(i+1, j)+")";

         myAllSubs.add(sunstr);


       }
   return myAllSubs;
  }

}
