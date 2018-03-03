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
package org.sosy_lab.cpachecker.core;
import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.cpachecker.util.AbstractStates.IS_TARGET_STATE;

import java.awt.Dimension;
import java.awt.Toolkit;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import javax.swing.JFrame;

import org.sosy_lab.common.AbstractMBean;
import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CFACreator;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CComplexTypeDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CTypeDefDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CArrayType;
import org.sosy_lab.cpachecker.cfa.types.c.CCompositeType;
import org.sosy_lab.cpachecker.cfa.types.c.CCompositeType.CCompositeTypeMemberDeclaration;
import org.sosy_lab.cpachecker.cfa.types.c.CElaboratedType;
import org.sosy_lab.cpachecker.cfa.types.c.CFunctionType;
import org.sosy_lab.cpachecker.cfa.types.c.CNamedType;
import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.CPAAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.ExternalCBMCAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.impact.ImpactAlgorithm;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.globalinfo.MyInfo;
import org.xidian.cpachecker.dz.MyCPA;
import org.xidian.cpachecker.dz.PathInfo;
import org.xidian.cpachecker.dz.Proposition;
import org.xidian.cpachecker.dz.TxtToXml;
import org.xidian.cpachecker.dz.Algorithm.ArrayCheckAlgorithm;
import org.xidian.cpachecker.dz.Algorithm.PointerCheckAlgorithm;
import org.xidian.cpachecker.dz.Algorithm.SimplePropertyCheckAlgorithm;
import org.xidian.cpachecker.dz.proposition.PropositionInfo;
import org.xidian.cpachecker.dz.util.PointerUtil;
import org.xidian.cpachecker.dz.util.SimplePropertyUtils;
import org.xidian.crl.CRLGlobal;
import org.xidian.dz.GUI.PropertyGUI;
import org.xidian.yk.Operators;

import com.google.common.base.Charsets;
import com.google.common.base.Joiner;
import com.google.common.io.Resources;
@Options(prefix="analysis")
public class CPAchecker {
  //加入自己的Map
  public static Map<String,Pair<String,String>> propositionsMap;
  public static Map<String,String> nameToLen;

  public static Map<String,Pair<String,String>> twoLens;
//  public static List<Pair<String,String>> subTwoLens=new ArrayList<Pair<String,String>>();
  public static Map<String,String> pureNameLen;
  public static Map<String,String> long_firstNameToPureLen;

  public static interface CPAcheckerMXBean {
    public int getReachedSetSize();

    public void stop();
  }

  private static class CPAcheckerBean extends AbstractMBean implements CPAcheckerMXBean {

    private final ReachedSet reached;
    private final Thread cpacheckerThread;

    public CPAcheckerBean(ReachedSet pReached, LogManager logger) {
      super("org.sosy_lab.cpachecker:type=CPAchecker", logger);
      reached = pReached;
      cpacheckerThread = Thread.currentThread();
      register();
    }

    @Override
    public int getReachedSetSize() {
      return reached.size();
    }

    @Override
    public void stop() {
      cpacheckerThread.interrupt();
    }

  }

  @Option(description="stop after the first error has been found")
  private boolean stopAfterError = true;

  @Option(name="disable",
      description="stop CPAchecker after startup (internal option, not intended for users)")
  private boolean disableAnalysis = false;

  @Option(name="externalCBMC",
      description="use CBMC as an external tool from CPAchecker")
  private boolean runCBMCasExternalTool = false;

  private final LogManager logger;
  private final Configuration config;
  private final CoreComponentsFactory factory;

  /**
   * This method will throw an exception if the user has requested CPAchecker to
   * stop immediately. This exception should not be caught by the caller.
   */
  public static void stopIfNecessary() throws InterruptedException {
    if (Thread.interrupted()) {
      throw new InterruptedException();
    }
  }

  // The content of this String is read from a file that is created by the
  // ant task "init".
  // To change the version, update the property in build.xml.
  private static final String version;
  static {
    String v = "(unknown version)";
    try {
      URL url = CPAchecker.class.getClassLoader().getResource("org/sosy_lab/cpachecker/VERSION.txt");
      if (url != null) {
        String content = Resources.toString(url, Charsets.US_ASCII).trim();
        if (content.matches("[a-zA-Z0-9 ._+:-]+")) {
          v = content;
        }
      }
    } catch (IOException e) {
      // Ignore exception, no better idea what to do here.
    }
    version = v;
  }

  public static String getVersion() {
    return version;
  }

  public CPAchecker(Configuration pConfiguration, LogManager pLogManager) throws InvalidConfigurationException {
    config = pConfiguration;
    logger = pLogManager;

    config.inject(this);
    factory = new CoreComponentsFactory(pConfiguration, pLogManager);
  }
  public CPAcheckerResult run1(String filename){
   //crl-start
    propositionsMap=new HashMap<String,Pair<String,String>>();//保存所有命题
    nameToLen=new HashMap<String,String>();
    twoLens=new HashMap<String,Pair<String,String>>();
    pureNameLen=new HashMap<String,String>();//记录普通数组名字和长度
    //crl-end
    Pair<ARGState,ARGState> errorState=null;
    logger.log(Level.INFO, "CPAchecker", getVersion(), "started");

    MainCPAStatistics stats = null;
    ReachedSet reached = null;
    Result result = Result.NOT_YET_STARTED;//enum类型

    try {
      stats = new MainCPAStatistics(config, logger);

      // create reached set, cpa, algorithm
      stats.creationTime.start();
      //MyCPA myCpa=null;
      Algorithm algorithm;
      CFA cfa = parse(filename, stats);
      Operators.cfa = cfa;
      //KeyVar.keyVarSet.add("a");
      Operators.initKeyVarSet();//<yangkai> 初始化关键变量集合，命题中涉及到的变量都为关键变量
      Operators.markKeyEdgesOfCFA(cfa);//<yangkai> 标记关键边
      HashMap<String, Set<Integer>> uselessBranches = new HashMap<String,Set<Integer>>() ;
      HashMap<String, Integer> equalToFinal = new HashMap<String,Integer>();
      String level="";
      FunctionExitNode exitNode=cfa.getMainFunction().getExitNode();
      MyInfo.callstack=""+cfa.getMainFunction().getNodeNumber();
        reached = factory.createReachedSet();
        if (runCBMCasExternalTool) {
          algorithm = new ExternalCBMCAlgorithm(filename, config, logger);
        } else {
          //CFA cfa = parse(filename, stats);//parsing the function.170
          GlobalInfo.getInstance().storeCFA(cfa);
          stopIfNecessary();
          ConfigurableProgramAnalysis cpa = factory.createCPA(cfa, stats);

          algorithm = factory.createAlgorithm(cpa, filename, cfa, stats);
          if (algorithm instanceof ImpactAlgorithm) {
            ImpactAlgorithm mcmillan = (ImpactAlgorithm)algorithm;//see1
            reached.add(mcmillan.getInitialState(cfa.getMainFunction()), mcmillan.getInitialPrecision(cfa.getMainFunction()));
          } else {
            initializeReachedSet(reached, cpa, cfa.getMainFunction());//seeing
          }
        }
        //mycode
        String propos="";
        Proposition proposition=null;//命题
        long time=0;
        if(algorithm instanceof SimplePropertyCheckAlgorithm){
            propos=SimplePropertyUtils.readProsition();//读命题
            proposition=new Proposition(propos);
            PropositionInfo.getInstance().propositionToCFAEdgeForSimpleProperty(logger, config, proposition);
            Set<CFANode> infiniteLoopHeadNode=SimplePropertyUtils.findInfiniteLoopHeadNode(cfa);
            time=System.currentTimeMillis();
            errorState=algorithm.run(reached,proposition,infiniteLoopHeadNode,cfa);
            time=System.currentTimeMillis()-time;
            result=reached.getResult();
        } else if(algorithm instanceof PointerCheckAlgorithm){
              PropositionInfo.getInstance().extractPropositions(cfa);
              Map<String,Pair<String,String>> propositionsMap=PropositionInfo.getInstance().getPropositionsMap();
              PointerUtil.writeAllPointers(propositionsMap);
              PropertyGUI pg=new PropertyGUI(propositionsMap,"please select a pointer :");
              pg.setSize(350,200);
              pg.setResizable(false);
              pg.choose();
              propos=PointerUtil.readProsition();
              proposition=new Proposition(propos);
              PropositionInfo.getInstance().propositionToCFAEdgeForPointer(logger, config, proposition);
              String funcAndVar=propos.substring(propos.indexOf("=>")+2,propos.indexOf("!=")).trim();
              String[] array=funcAndVar.split("::");
              PathInfo pathInfo=new PathInfo();
              boolean hasUsed=pathInfo.analysisCFA(cfa, exitNode,array[0],array[1], level, uselessBranches, equalToFinal);
              if(hasUsed){
              MyInfo.uselessBranches=uselessBranches;
              MyInfo.equalToFinal=equalToFinal;
              time=System.currentTimeMillis();
              errorState=algorithm.run(reached,proposition,null,cfa);
              time=System.currentTimeMillis()-time;
              result=reached.getResult();
              }
              else{
                result=Result.SAFE;
                time=0;
              }
        }
        else if(algorithm instanceof ArrayCheckAlgorithm){
          PropositionInfo.getInstance().extractPropositionsForArray(cfa);
          Map<String,Pair<String,String>> propositionsMap=PropositionInfo.getInstance().getPropositionsMap();
          PointerUtil.writeAllPointers(propositionsMap);
          PropertyGUI pg=new PropertyGUI(propositionsMap,"请选择你要检查的数组:");
          pg.setSize(350,200);
          pg.setResizable(false);
          pg.choose();
          propos=PointerUtil.readProsition();
          proposition=new Proposition(propos);
          PropositionInfo.getInstance().propositionToCFAEdgeForArray(logger, config, proposition);
          time=System.currentTimeMillis();
          errorState=algorithm.run(reached,proposition,null,null);
          time=System.currentTimeMillis()-time;
          result=reached.getResult();
        }
        else{
          time=System.currentTimeMillis();
          boolean isComplete=runAlgorithm(algorithm,reached,stats);
          time=System.currentTimeMillis()-time;
          result=analyzeResult(reached, isComplete);
        }

        /*else if(algorithm instanceof ){ //数组越界

        }*/
        //mycodeend
        printConfigurationWarnings();

        stats.creationTime.stop();
        stopIfNecessary();
        // now everything necessary has been instantiated
        if (disableAnalysis) {
          return new CPAcheckerResult(Result.NOT_YET_STARTED, null, null);
        }
        // run analysis

//        File output=new File("D:\\property\\AllOutputs.txt");
//        FileOutputStream fr=new FileOutputStream (output,true);
//        assert fr!=null;
//        //fr.write(Byte.valueOf(result.toString()+":"+var.substring(0,var.indexOf("!"))));
//        //PrintWriter  pr=new PrintWriter (fr);
//        String message=result.toString()+":"+propos.substring(0,propos.indexOf("!"))+"---->"+time+"  ms"+"\r\n";
//        byte[] by=message.getBytes();
//        fr.write(by);
//        fr.close();
        //TxtToXml ttx=new TxtToXml();
        //ttx.createXml();

    } catch (IOException e) {
      logger.logUserException(Level.SEVERE, e, "Could not read file");

    } catch (ParserException e) {
      // only log message, not whole exception because this is a C problem,
      // not a CPAchecker problem
      logger.logUserException(Level.SEVERE, e, "Parsing failed");
      logger.log(Level.INFO, "Make sure that the code was preprocessed using Cil (HowTo.txt).\n"
          + "If the error still occurs, please send this error message together with the input file to cpachecker-users@sosy-lab.org.");

    } catch (InvalidConfigurationException e) {
      logger.logUserException(Level.SEVERE, e, "Invalid configuration");

    } catch (InterruptedException e) {
      // CPAchecker must exit because it was asked to
      // we return normally instead of propagating the exception
      // so we can return the partial result we have so far

    } catch (CPAException e) {
      logger.logUserException(Level.SEVERE, e, null);
    }
    return new CPAcheckerResult(result, reached, stats);


  }
  public  CPAcheckerResult run(String filename) {

    logger.log(Level.INFO, "CPAchecker", getVersion(), "started");

    Pair<ARGState, ARGState> errorState=null;
    MainCPAStatistics stats = null;
    ReachedSet reached = null;
    Result result = Result.NOT_YET_STARTED;//enum类型

    try {
      stats = new MainCPAStatistics(config, logger);

      // create reached set, cpa, algorithm
      stats.creationTime.start();

//duan的CPA方法============================================================================开始
      MyCPA myCpa=null;
      Algorithm algorithm;
      CFA cfa = parse(filename, stats);

      //提取命题
   propositionsMap=new HashMap<String,Pair<String,String>>();//保存所有命题
   nameToLen=new HashMap<String,String>();
  Map<String,String> temp_nameToLen=new HashMap<String,String>();
   twoLens=new HashMap<String,Pair<String,String>>();
   pureNameLen=new HashMap<String,String>();//记录普通数组名字和长度


   Map<String,String> long_nameToLen=new HashMap<String,String>();//暂时记录加入的指向数组的指针
    long_firstNameToPureLen=new HashMap<String,String>();//记录指针和第一次初始长度==
   Map<String,String>  long_tempNameToPureLen=new HashMap<String,String>();//记录指针和初始长度==例如p=a;p=b;q=p,第一次记录<p,a.len>,第二次记录<p,b.len>,第三次记录<q,b.len>

   //结构体两个结构
   Map<Pair<String,String>,Pair<String,String>> tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();//记录定义结构<student1::a,length>
   Map<String,String> lastnameTOarrlen=new HashMap<String,String>();//记录声明语句结构：<std.a,length> <std.std1.a,lenth>

   List<CFAEdge> funcalledges=new ArrayList<CFAEdge>();

      //extractPropositions(cfa,propositionsMap);//==============================================消除dz==1

      //=====提取数组相应length长度==========================================================================龙开始======

      //龙开发代码===============记录所有数组=========================
    //  Map<String,BigInteger> arrNameLen=new HashMap<String,BigInteger>();
      for(CFANode node:cfa.getAllNodes()){
       // System.out.println(nameToLen);
        for(int edgeIdx=0;edgeIdx<node.getNumLeavingEdges();edgeIdx++){
          CFAEdge edge=node.getLeavingEdge(edgeIdx);
         // System.out.println(edge.toString());
         switch(edge.getEdgeType()){
         //===============================================================================================1.指针
         case StatementEdge:

           CStatementEdge statementEdge=(CStatementEdge)edge;
           CStatement expression= statementEdge.getStatement();
           if(expression instanceof CAssignment){
             CAssignment assignmentExpression=(CAssignment)expression;
             CExpression op1=assignmentExpression.getLeftHandSide();
             CRightHandSide op2= assignmentExpression.getRightHandSide();
             if(op1 instanceof CIdExpression){
              CIdExpression op1IdExp=(CIdExpression)op1;
              String op1PointerName= op1IdExp.getName();
              String op1funcname=node.getFunctionName();
              String op1fullname=op1funcname+"::"+op1PointerName;
              boolean funparaarr=false;
              if(CPAchecker.nameToLen.containsKey(op1fullname)){
                if(CPAchecker.nameToLen.get(op1fullname).equals("function_parameter_array")){
                  funparaarr=true;
                }
              }
              if((op1IdExp.getExpressionType() instanceof CPointerType)&&(!funparaarr)){//op1是指针形式

                //System.out.println(op2.getExpressionType());
                if((op2.getExpressionType() instanceof CPointerType)&&(op2 instanceof CIdExpression)){//1.op2也是指针形式q=p形式===================注意：考虑p=q+1或p=q-1等此处没有考虑================注意啊


                  CIdExpression op2IdExp=(CIdExpression)op2;
                  String arrName=op2IdExp.getName();
                  Set<String> pointernameKeys=long_tempNameToPureLen.keySet();
                  for(String pointernameKey:pointernameKeys){

                    int a=pointernameKey.indexOf("::");
                   String pointernameKey1=pointernameKey.substring(a+2).trim();
                    if(pointernameKey1.trim().equals(arrName.trim())){//例如q=p表示 temp中有p，当前p指向数组,arrName是op2name

                      Set<String> myFirstPureLenToNames=long_firstNameToPureLen.keySet();
                      String  function=node.getFunctionName();//注意处理global情形======注意
                      //}

                      arrName=op1IdExp.getName();
                     String exArrName=function+"::"+arrName;//记录op1中q全名


                      String myTempPointerLen =long_tempNameToPureLen.get(pointernameKey);//记录数组长度，指针指向===如q=p,找到p指针的数组长度

                      if(!myFirstPureLenToNames.contains(exArrName)){
                        String arrNameop1=op1IdExp.getName();
                        String exArrNameop1=function+"::"+arrNameop1;
                         String first="al=>"+exArrNameop1+" < length";
                         String second="au=>"+exArrNameop1+" == "+exArrNameop1;
                         propositionsMap.put(exArrNameop1,Pair.of(first, second));
                         long_tempNameToPureLen.put(exArrNameop1, myTempPointerLen);
                         long_firstNameToPureLen.put(exArrNameop1, myTempPointerLen);

                      }else{
                        String arrNameop1=op1IdExp.getName();
                        String exArrNameop1=function+"::"+arrNameop1;
                         String first="al=>"+exArrNameop1+" < length";
                         String second="au=>"+exArrNameop1+" == "+exArrNameop1;
                         propositionsMap.put(exArrNameop1,Pair.of(first, second));
                         long_tempNameToPureLen.put(exArrNameop1, myTempPointerLen);
                      }




                      }

                    }



                }//右边是指针的形式结束
                else{
                 String op2Str= op2.toASTString();
                 boolean myflag=false;//表示是否是a+huo+a此种形式
                 String op2StrNoSpace=op2Str.replaceAll(" ", "");
                 Set<String> nameKeys=nameToLen.keySet();
                 String function=node.getFunctionName();
                 String op2name=function+"::"+op2Str;
                 String tempA = null;
                 for(String nameKey:nameKeys){
                   int a=nameKey.indexOf("::");
                   String nameKeyPure=nameKey.substring(a+2).trim();
                   if(op2StrNoSpace.matches(nameKeyPure.trim()+"\\+.*")||op2StrNoSpace.matches(".*\\+"+nameKeyPure.trim())){
                      tempA =nameKeyPure;
                     myflag=true;

                   }

                 }
                   if(nameKeys.contains(op2name)){//第一中情形：a数组名，加入p
                    /* if(statementEdge.getStatement().){
                       function="Global";
                     }else{*/

                     //}
                     String arrName=op1IdExp.getName();

                    String exArrName=function+"::"+arrName;

                    String myTempPointerLen =nameToLen.get(op2name);//记录数组长度，指针指向===如p=a,找到a数组长度
                     String first="al=>"+exArrName+" < length";

                     String second="au=>"+exArrName+" == "+exArrName;
                     propositionsMap.put(exArrName,Pair.of(first, second));
                  //   long_nameToLen.put(exArrName, "pointer_array");

                    Set<String> myTempPureLenToNames=long_tempNameToPureLen.keySet();

                     if(long_tempNameToPureLen.isEmpty()){
                       long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                       long_firstNameToPureLen.put(exArrName, myTempPointerLen);//注意，第一个肯定是指针指向数组
                     }
                     else if(!(myTempPureLenToNames.contains(exArrName))){
                     long_firstNameToPureLen.put(exArrName, myTempPointerLen);
                       long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                     }else{
                     long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                     }

                   }
                   else if(myflag){//第二种情形：a+或+a


                     CRLGlobal.getInstance().setPointerGloLen(op2Str.replaceAll(tempA,"0"));
                       function=node.getFunctionName();
                     String arrName=op1IdExp.getName();

                     String exArrName=function+"::"+arrName;
                     String exArrName1=function+"::"+tempA;
                     String myTempPointerLen =nameToLen.get(exArrName1);//记录数组长度，指针指向===如p=a+1,找到a数组长度
                      String first="al=>"+exArrName+" < length";
                      String second="au=>"+exArrName+" == "+exArrName;
                      propositionsMap.put(exArrName,Pair.of(first, second));
                    //  long_nameToLen.put(exArrName, "pointer_array");
                      Set<String> myTenpPureLenToNames=long_tempNameToPureLen.keySet();

                      if(long_tempNameToPureLen.isEmpty()){
                        long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                        long_firstNameToPureLen.put(exArrName, myTempPointerLen);//注意，第一个肯定是指针指向数组
                      }
                      if(!(myTenpPureLenToNames.contains(exArrName))){
                        long_firstNameToPureLen.put(exArrName, myTempPointerLen);
                        long_tempNameToPureLen.put(exArrName, myTempPointerLen);
                      }
                      long_tempNameToPureLen.put(exArrName, myTempPointerLen);

                   }else{//即左边是指针形式，右边不是指针，不是a，不是a+形式，得看看long_tempNameToPureLen里是否有此指针，有的话，把次记录去除
                     Set<String> myTenpPureLenToNames=long_tempNameToPureLen.keySet();
                       function=node.getFunctionName();//注意处理global情形======注意
                     //}
                     String arrName=op1IdExp.getName();

                    String exArrName=function+"::"+arrName;
                     if(myTenpPureLenToNames.contains(exArrName)){
                       long_tempNameToPureLen.remove(exArrName);                     }

                   }


                }//else在此处结束
              }
            }


         }
           Map<String,String> temp_long_nameToLen=long_firstNameToPureLen;

           for(Map.Entry<String,String> entry:temp_long_nameToLen.entrySet()){
            entry.setValue("pointer_array");
           }
         nameToLen.putAll(temp_long_nameToLen);




          break;
        //================================================================================================2.方法调用
         case FunctionCallEdge:

           funcalledges.add(edge);

           break;//待解决=======================================方法调用中用到声明数组，得考虑


           //==================================================================================================3.声明语句：包括一般数组处理和结构体处理
         case DeclarationEdge:
           CDeclarationEdge declarationEdge=(CDeclarationEdge)edge;
           String function="";
           CType type=declarationEdge.getDeclaration().getType();
           if(declarationEdge.getDeclaration().isGlobal()){
             function="Global";
           }else{
             function=node.getFunctionName();
           }
           String arrName=declarationEdge.getDeclaration().getName();//struct student std；===是std
            if(type instanceof CArrayType){//=======================================================================3.1:一般数组 he 结构体数组  处理
                    CArrayType arr=(CArrayType)declarationEdge.getDeclaration().getType();
                    if(arr.getType() instanceof CArrayType){//===================简单二维数组处理
                   String  secondLenStr= arr.getLength().toASTString();
                   CArrayType arrArr=(CArrayType)arr.getType();
                   String firstLenStr=arrArr.getLength().toASTString();
                   arrName=function+"::"+arrName;
                   String first="al=>"+arrName+" < length";
                   String second="au=>"+arrName+" == "+arrName;
                   propositionsMap.put(arrName,Pair.of(first, second));
                   nameToLen.put(arrName, "two_array");
                   twoLens.put(arrName, Pair.of(firstLenStr, secondLenStr));

                    }else if(arr.getType() instanceof CSimpleType){//========================================================简单一维数组
                      if(arr.getLength()!=null){
                    String arrLenStr=arr.getLength().toASTString();
                    arrName=function+"::"+arrName;
                    String first="al=>"+arrName+" < length";
                    String second="au=>"+arrName+" == "+arrName;
                    propositionsMap.put(arrName,Pair.of(first, second));
                    nameToLen.put(arrName, arrLenStr);
                    pureNameLen.put(arrName, arrLenStr);
                      }
                    }else if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){//外部声明结构体数组：：：struct student std[2]

                      //CArrayType arrType=(CArrayType)arr.getType();
                      String name2=arrName;//得到std名字
                      int structArrLen=0;
                      if(arr.getLength() instanceof CIntegerLiteralExpression){
                         structArrLen=((CIntegerLiteralExpression)arr.getLength()).getValue().intValue();
                      }
                      if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){
                        String name1=null;
                        if(arr.getType() instanceof CElaboratedType){
                        CElaboratedType elaType=(CElaboratedType)arr.getType();
                        name1= elaType.getName();//student===类型名字
                        }else if(arr.getType() instanceof CNamedType){
                          CNamedType elaType=(CNamedType)arr.getType();
                          name1= elaType.getName();//STUDENT===类型名字
                        }
                       //看temp中是否有student，有的话则加入到nameToLen
                       if(!(tempnameTOarrlen.isEmpty())){
                         Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                         for(Pair<String,String> tempname:tempnames){
                          String first= tempname.getFirst();
                          String second=tempname.getSecond();
                          if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入std[0].a和std[1].a
                            for(int structarrlen=0;structarrlen<structArrLen;structarrlen++){
                            String structArrName="("+name2+"["+structarrlen+"])"+"."+second;
                            //String structArrName1=name2+"->"+second;
                            Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                            String firstlenstr=lens.getFirst();
                            String secondlenstr=lens.getSecond();
                            if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体数组外部声明
                            String arrLenStr= firstlenstr;

                            arrName=function+"::"+structArrName;
                            String first1="al=>"+arrName+" < length";
                            String second1="au=>"+arrName+" == "+arrName;
                            propositionsMap.put(arrName,Pair.of(first1, second1));
                            nameToLen.put(arrName, arrLenStr);
                            pureNameLen.put(arrName, arrLenStr);


                            }else{//========================================二维数组碰到结构体数组外部声明
                              arrName=function+"::"+structArrName;
                              String first1="al=>"+arrName+" < length";
                              String second1="au=>"+arrName+" == "+arrName;
                              propositionsMap.put(arrName,Pair.of(first1, second1));
                              nameToLen.put(arrName, "two_array");
                              twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                              pureNameLen.put(arrName, "two_array");


                            }
                            }
                            }
                          }
                         }

                      }





                    }
            }else if(declarationEdge.getDeclaration() instanceof CComplexTypeDeclaration){//==============================3.2.1结构体 定义处理
              Map<Pair<String,String>,Pair<String,String>> temp_tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();
              CComplexTypeDeclaration comDec=(CComplexTypeDeclaration)declarationEdge.getDeclaration();
              if(comDec.getType() instanceof CCompositeType){
              CCompositeType comType=(CCompositeType)comDec.getType();
             String structName= comType.getName();//记录结构体名字，如student
             List<CCompositeTypeMemberDeclaration> listMembs=comType.getMembers();
             for(CCompositeTypeMemberDeclaration listMemb:listMembs ){
               if(listMemb.getType() instanceof CArrayType){//===================================定义中碰到数组
                String structArrName= listMemb.getName();//记录数组名字，如a
                 CArrayType arr=(CArrayType)listMemb.getType();
                 if(arr.getType() instanceof CArrayType){//===================简单二维数组处理
                   String  secondLenStr= arr.getLength().toASTString();
                   CArrayType arrArr=(CArrayType)arr.getType();
                   String firstLenStr=arrArr.getLength().toASTString();

                   tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstLenStr, secondLenStr));

                    }else if(arr.getType() instanceof CSimpleType){//==========================================================一维数组处理
                      String structArrLen= arr.getLength().toASTString();//记录数组长度lenth
                      tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(structArrLen, "str_one_array"));


                    }else if((arr.getType() instanceof CElaboratedType)||(arr.getType() instanceof CNamedType)){//===========碰到结构体定义中内部声明： struct student1 std3[2];


                      String name2= listMemb.getName();//std1=====对象名字
                      int structArrLen=((CIntegerLiteralExpression)arr.getLength()).getValue().intValue();
                      String name1=null;
                      if(arr.getType() instanceof CElaboratedType){
                      CElaboratedType elaType=(CElaboratedType)arr.getType();
                      name1= elaType.getName();//student1===类型名字
                      }else if(arr.getType() instanceof CNamedType){
                        CNamedType elaType=(CNamedType)arr.getType();
                        name1= elaType.getName();//STUDENT1===类型名字
                      }

                     if(!(tempnameTOarrlen.isEmpty())){
                     Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                     for(Pair<String,String> tempname:tempnames){
                      String first= tempname.getFirst();
                      String second=tempname.getSecond();
                      if(first.equals(name1)){//表示有数组====存两个：temp和nameToLen 即：<student::std1.a,length>和<global::std1.a,length>
                        for(int structarrlen=0;structarrlen<structArrLen;structarrlen++){
                       // String  structfunction="Global";
                         structArrName="("+name2+"["+structarrlen+"])"+"."+second;
                        Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                        String firstlenstr=lens.getFirst();
                        String secondlenstr=lens.getSecond();
                        if(secondlenstr.equals("str_one_array")){//==========一维数组碰到内部声明
                          String arrLenStr= firstlenstr;
                          temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                          /*arrName=structfunction+"::"+structArrName;
                          String first1="d=>"+arrName+" < length";
                          String second1="r=>"+arrName+" == "+arrName;
                          propositionsMap.put(arrName,Pair.of(first1, second1));
                          nameToLen.put(arrName, arrLenStr);
                          pureNameLen.put(arrName, arrLenStr);*/
                        }else{//===========================================二维数组碰到内部声明
                          temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                          /*arrName=structfunction+"::"+structArrName;
                          String first1="d=>"+arrName+" < length";
                          String second1="r=>"+arrName+" == "+arrName;
                          propositionsMap.put(arrName,Pair.of(first1, second1));
                          nameToLen.put(arrName, "two_array");
                          twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                          pureNameLen.put(arrName, "two_array");*/
                        }

                      }
                      }
                     }

                     }


                 }
               }
               if((listMemb.getType() instanceof CElaboratedType)||(listMemb.getType() instanceof CNamedType)){//==============================定义中碰到结构体声明==内部声明

                String name2= listMemb.getName();//std1=====对象名字
                String name1=null;
                if(listMemb.getType() instanceof CElaboratedType){
                CElaboratedType elaType=(CElaboratedType)listMemb.getType();
                name1= elaType.getName();//student1===类型名字
                }else if(listMemb.getType() instanceof CNamedType){
                  CNamedType elaType=(CNamedType)listMemb.getType();
                  name1= elaType.getName();//STUDENT1===类型名字
                }

               if(!(tempnameTOarrlen.isEmpty())){
               Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
               for(Pair<String,String> tempname:tempnames){
                String first= tempname.getFirst();
                String second=tempname.getSecond();
                if(first.equals(name1)){//表示有数组====存两个：temp和nameToLen 即：<student::std1.a,length>和<global::std1.a,length>
                  //String  structfunction="Global";
                  String structArrName=name2+"."+second;
                  Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                  String firstlenstr=lens.getFirst();
                  String secondlenstr=lens.getSecond();
                  if(secondlenstr.equals("str_one_array")){//==========一维数组碰到内部声明
                    String arrLenStr= firstlenstr;
                    temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                    /*arrName=structfunction+"::"+structArrName;
                    String first1="d=>"+arrName+" < length";
                    String second1="r=>"+arrName+" == "+arrName;
                    propositionsMap.put(arrName,Pair.of(first1, second1));
                    nameToLen.put(arrName, arrLenStr);
                    pureNameLen.put(arrName, arrLenStr);*/
                  }else{//===========================================二维数组碰到内部声明
                    temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                    /*arrName=structfunction+"::"+structArrName;
                    String first1="d=>"+arrName+" < length";
                    String second1="r=>"+arrName+" == "+arrName;
                    propositionsMap.put(arrName,Pair.of(first1, second1));
                    nameToLen.put(arrName, "two_array");
                    twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                    pureNameLen.put(arrName, "two_array");*/
                  }

                }
               }

               }
               }else if(listMemb.getType() instanceof CPointerType){

                 CPointerType pointerType=(CPointerType)listMemb.getType();
                 if((pointerType.getType() instanceof CElaboratedType)||(pointerType.getType() instanceof CNamedType)){
                   String name2= listMemb.getName();//std1=====对象名字
                   String name1=null;
                   if(listMemb.getType() instanceof CElaboratedType){
                   CElaboratedType elaType=(CElaboratedType)listMemb.getType();
                   name1= elaType.getName();//student===类型名字
                   }else if(listMemb.getType() instanceof CNamedType){
                     CNamedType elaType=(CNamedType)listMemb.getType();
                     name1= elaType.getName();//STUDENT===类型名字
                   }
                  //看temp中是否有student，有的话则加入到nameToLen
                  if(!(tempnameTOarrlen.isEmpty())){
                    Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                    for(Pair<String,String> tempname:tempnames){
                     String first= tempname.getFirst();
                     String second=tempname.getSecond();
                     if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入两个：(*pp).a  和 pp->a
                       String structArrName="("+"*("+name2+")"+"."+second+")";
                       String structArrName1=name2+"->"+second;//==========================================================================调试
                       Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                       String firstlenstr=lens.getFirst();
                       String secondlenstr=lens.getSecond();
                       if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体指针内部声明
                       String arrLenStr= firstlenstr;
                       temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(arrLenStr,"str_one_array"));
                      /* arrName=function+"::"+structArrName;
                       String first1="d=>"+arrName+" < length";
                       String second1="r=>"+arrName+" == "+arrName;
                       propositionsMap.put(arrName,Pair.of(first1, second1));
                       nameToLen.put(arrName, arrLenStr);
                       pureNameLen.put(arrName, arrLenStr);*/
                       temp_tempnameTOarrlen.put(Pair.of(structName, structArrName1), Pair.of(arrLenStr,"str_one_array"));
                       /*arrName=function+"::"+structArrName1;
                        first1="d=>"+arrName+" < length";
                       second1="r=>"+arrName+" == "+arrName;
                       propositionsMap.put(arrName,Pair.of(first1, second1));
                       nameToLen.put(arrName, arrLenStr);
                       pureNameLen.put(arrName, arrLenStr);*/
                       }else{//========================================二维数组碰到结构体指针内部声明
                         temp_tempnameTOarrlen.put(Pair.of(structName, structArrName), Pair.of(firstlenstr, secondlenstr));
                         /*arrName=function+"::"+structArrName;
                         String first1="d=>"+arrName+" < length";
                         String second1="r=>"+arrName+" == "+arrName;
                         propositionsMap.put(arrName,Pair.of(first1, second1));
                         nameToLen.put(arrName, "two_array");
                         twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                         pureNameLen.put(arrName, "two_array");*/
                         temp_tempnameTOarrlen.put(Pair.of(structName, structArrName1), Pair.of(firstlenstr, secondlenstr));
                        /* arrName=function+"::"+structArrName1;
                         first1="d=>"+arrName+" < length";
                        second1="r=>"+arrName+" == "+arrName;
                        propositionsMap.put(arrName,Pair.of(first1, second1));
                         nameToLen.put(arrName, "two_array");
                         twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                         pureNameLen.put(arrName, "two_array");*/
                       }
                       }
                     }
                    }

                 }
               }

             }
            }
             tempnameTOarrlen.putAll(temp_tempnameTOarrlen);

            }else if(declarationEdge.getDeclaration() instanceof CTypeDefDeclaration){//处理typedef定义问题外部定义=======把student变成STUDENT
              Map<Pair<String,String>,Pair<String,String>> temp_tempnameTOarrlen=new HashMap<Pair<String,String>,Pair<String,String>>();
              List<Pair<String,String>> temp_removepa=new ArrayList<Pair<String,String>>();
              CTypeDefDeclaration typedefDec=(CTypeDefDeclaration)declarationEdge.getDeclaration();
             String name2= typedefDec.getName();
             if(typedefDec.getType() instanceof CElaboratedType){
               CElaboratedType elaType=(CElaboratedType)typedefDec.getType();
              String name1= elaType.getName();
              if(!(tempnameTOarrlen.isEmpty())){
                Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                for(Pair<String,String> tempname:tempnames){
                 String first= tempname.getFirst();
                 String second=tempname.getSecond();
                 if(first.equals(name1)){
                   Pair<String,String> lens=tempnameTOarrlen.get(tempname);

                   temp_tempnameTOarrlen.put(Pair.of(name2, second), lens);
                   temp_removepa.add(tempname);

                 }
                }
                tempnameTOarrlen.putAll(temp_tempnameTOarrlen);
                for(Pair<String,String> removpair:temp_removepa){
                  tempnameTOarrlen.remove(removpair);
                }
                }
             }



            }else if(declarationEdge.getDeclaration() instanceof CVariableDeclaration){//====================================3.2.2结构体 外面声明处理
              CVariableDeclaration  variDec=(CVariableDeclaration)declarationEdge.getDeclaration();
             String name2= variDec.getName();//std===如果是指针则是pp======对象名字=====================================下面都要用到name2
              if((variDec.getType() instanceof CElaboratedType)||(variDec.getType() instanceof CNamedType)){//=============================struct student std;
                String name1=null;
                if(variDec.getType() instanceof CElaboratedType){
                CElaboratedType elaType=(CElaboratedType)variDec.getType();
                name1= elaType.getName();//student===类型名字
                }else if(variDec.getType() instanceof CNamedType){
                  CNamedType elaType=(CNamedType)variDec.getType();
                  name1= elaType.getName();//STUDENT===类型名字
                }
               if(!(tempnameTOarrlen.isEmpty())){
               Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
               for(Pair<String,String> tempname:tempnames){
                String first= tempname.getFirst();
                String second=tempname.getSecond();
                if(first.equals(name1)){

                  String structArrName=name2+"."+second;
                  Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                  String firstlenstr=lens.getFirst();
                  String secondlenstr=lens.getSecond();
                  if(secondlenstr.equals("str_one_array")){

                  String arrLenStr= firstlenstr;

                  arrName=function+"::"+structArrName;
                  String first1="al=>"+arrName+" < length";
                  String second1="au=>"+arrName+" == "+arrName;
                  propositionsMap.put(arrName,Pair.of(first1, second1));
                  nameToLen.put(arrName, arrLenStr);
                  pureNameLen.put(arrName, arrLenStr);
                  }else{
                    arrName=function+"::"+structArrName;
                    String first1="al=>"+arrName+" < length";
                    String second1="au=>"+arrName+" == "+arrName;
                    propositionsMap.put(arrName,Pair.of(first1, second1));
                    nameToLen.put(arrName, "two_array");
                    twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                    pureNameLen.put(arrName, "two_array");
                  }

                }
               }
               }
              }

              if(variDec.getType() instanceof CPointerType){
                CPointerType pointerType=(CPointerType)variDec.getType();
                if((pointerType.getType() instanceof CElaboratedType)||(pointerType.getType() instanceof CNamedType)){
                  String name1=null;
                  if(pointerType.getType() instanceof CElaboratedType){
                  CElaboratedType elaType=(CElaboratedType)pointerType.getType();
                  name1= elaType.getName();//student===类型名字
                  }else if(pointerType.getType() instanceof CNamedType){
                    CNamedType elaType=(CNamedType)pointerType.getType();
                    name1= elaType.getName();//STUDENT===类型名字
                  }
                 //看temp中是否有student，有的话则加入到nameToLen
                 if(!(tempnameTOarrlen.isEmpty())){
                   Set<Pair<String,String>>  tempnames= tempnameTOarrlen.keySet();
                   for(Pair<String,String> tempname:tempnames){
                    String first= tempname.getFirst();
                    String second=tempname.getSecond();
                    if(first.equals(name1)){//有，当数组名来用，而不是指针来用,加入两个：(*pp).a  和 pp->a
                      String structArrName="(*"+name2+")"+"."+second;
                      String structArrName1=name2+"->"+second;
                      Pair<String,String> lens=tempnameTOarrlen.get(tempname);
                      String firstlenstr=lens.getFirst();
                      String secondlenstr=lens.getSecond();
                      if(secondlenstr.equals("str_one_array")){//=======一维数组碰到结构体指针外部声明
                      String arrLenStr= firstlenstr;

                      arrName=function+"::"+structArrName;
                      String first1="al=>"+arrName+" < length";
                      String second1="au=>"+arrName+" == "+arrName;
                      propositionsMap.put(arrName,Pair.of(first1, second1));
                      nameToLen.put(arrName, arrLenStr);
                      pureNameLen.put(arrName, arrLenStr);

                      arrName=function+"::"+structArrName1;
                       first1="al=>"+arrName+" < length";
                      second1="au=>"+arrName+" == "+arrName;
                      propositionsMap.put(arrName,Pair.of(first1, second1));
                      nameToLen.put(arrName, arrLenStr);
                      pureNameLen.put(arrName, arrLenStr);
                      }else{//========================================二维数组碰到结构体指针外部声明
                        arrName=function+"::"+structArrName;
                        String first1="al=>"+arrName+" < length";
                        String second1="au=>"+arrName+" == "+arrName;
                        propositionsMap.put(arrName,Pair.of(first1, second1));
                        nameToLen.put(arrName, "two_array");
                        twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                        pureNameLen.put(arrName, "two_array");

                        arrName=function+"::"+structArrName1;
                        first1="al=>"+arrName+" < length";
                       second1="au=>"+arrName+" == "+arrName;
                       propositionsMap.put(arrName,Pair.of(first1, second1));
                        nameToLen.put(arrName, "two_array");
                        twoLens.put(arrName, Pair.of(firstlenstr, secondlenstr));
                        pureNameLen.put(arrName, "two_array");
                      }
                      }
                    }
                   }

                }
              }
            }

         }
        }

      }

      //提取结束=========================================================================================================龙结束
     // long_extractPropositions(cfa,propositionsMap);
      for(CFAEdge edge:funcalledges){
        CFunctionCallEdge functionCallEdge=(CFunctionCallEdge)edge;
        //=======================================================只是方法调用，此方法无返回值，如fun(a)
        if(functionCallEdge.getFunctionCall() instanceof CFunctionCallStatement){
          Map<String,Pair<String,String>> long_propositionsMap=new HashMap<String,Pair<String,String>>();
          CFunctionCallStatement funSta=(CFunctionCallStatement)functionCallEdge.getFunctionCall();

          CFunctionCallExpression funExp=funSta.getFunctionCallExpression();
         String funname= funExp.getFunctionNameExpression().toASTString();//得到方法名字
          //System.out.println(funExp.getFunctionNameExpression().toASTString());
          List<CExpression> paras=funExp.getParameterExpressions();

          for(int i=0;i<paras.size();i++){
           CExpression para=paras.get(i);
            String parastr=para.toASTString().trim();

            Set<String> arrNames=nameToLen.keySet();
            for(String arrName:arrNames){
              int a=arrName.indexOf("::");
              String changeArrName=arrName.substring(a+2).trim();
              if(parastr.contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入

                  CFunctionDeclaration fundec= (CFunctionDeclaration) funExp.getDeclaration();
                  CFunctionType funType=fundec.getType();
                 CParameterDeclaration cparadec= funType.getParameters().get(i);
                String xingName= cparadec.getName();
                   String exArrName= xingName;
                   String function="";
                   /*if(funDec.isGlobal()){
                     function="Global";
                   }else{
                     function=node.getFunctionName();
                   }*/
                   function=funname;
                   exArrName=function+"::"+exArrName;
                   String first="al=>"+exArrName+" < length";
                   String second="au=>"+exArrName+" == "+exArrName;
                   long_propositionsMap.put(exArrName,Pair.of(first, second));
                   temp_nameToLen.put(exArrName, "function_parameter_array");



              }
            }



          }
          propositionsMap.putAll(long_propositionsMap);
          nameToLen.putAll(temp_nameToLen);
        }//整个if结束，没有赋值的if
     //======================================================================有返回值的方法调用，赋值，如c=fun(a);
        if(functionCallEdge.getFunctionCall() instanceof CFunctionCallAssignmentStatement){
          Map<String,Pair<String,String>> long_propositionsMap=new HashMap<String,Pair<String,String>>();
          CFunctionCallAssignmentStatement funSta=(CFunctionCallAssignmentStatement)functionCallEdge.getFunctionCall();
           CFunctionCallExpression funRight= funSta.getRightHandSide();


           List<CExpression> paras=funRight.getParameterExpressions();
           for(int i=0;i<paras.size();i++){
             CExpression para=paras.get(i);
             String parastr=para.toASTString().trim();

             Set<String> arrNames=nameToLen.keySet();
             for(String arrName:arrNames){
               int a=arrName.indexOf("::");
               String changeArrName=arrName.substring(a+2).trim();
               if(parastr.trim().contains(changeArrName)){//判断是否参数里有与检验加入的数组名，有的话进入

                 CFunctionDeclaration fundec= (CFunctionDeclaration) funRight.getDeclaration();
                 CFunctionType funType=fundec.getType();
                CParameterDeclaration cparadec= funType.getParameters().get(i);
               String xingName= cparadec.getName();
                  String exArrName= xingName;

                    String function="";
                    /*if(funDec.isGlobal()){
                      function="Global";
                    }else{
                      function=node.getFunctionName();
                    }*/
                    CIdExpression funRightExp=(CIdExpression)funRight.getFunctionNameExpression();
                    String funName=funRightExp.getName();//得到方法名字===fun
                    function=funName;
                    exArrName=function+"::"+exArrName;
                    String first="al=>"+exArrName+" < length";
                    String second="au=>"+exArrName+" == "+exArrName;
                    long_propositionsMap.put(exArrName,Pair.of(first, second));
                    temp_nameToLen.put(exArrName, "function_parameter_array");



               }
             }

           }
           propositionsMap.putAll(long_propositionsMap);
           nameToLen.putAll(temp_nameToLen);
        }

      }

       System.out.println(nameToLen);
       System.out.println(propositionsMap);

      //往"D:\\property\\allPointers.txt"中写入所有点，包括所有指针和其对应的    d  和    r================================================写入所有点
      FileWriter fw=new FileWriter("D:\\property\\allPointers.txt");
      assert fw!=null;
      BufferedWriter bw=new BufferedWriter(fw);
      Iterator<String> it=propositionsMap.keySet().iterator();
      while(it.hasNext()){
        String s=it.next();
        s=s+"<->{ "+propositionsMap.get(s).getFirst()+"&&"+propositionsMap.get(s).getSecond()+" }";
        bw.write(s+"\r\n");
        bw.flush();
      }
      bw.close();

      //GUI建立过程========================================GUI开始
      PropertyGUI pg=new PropertyGUI(propositionsMap," ");
      pg.setSize(350,200);
      pg.setResizable(false);
      Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
      int x = (screenSize.width-pg.getWidth())/2;
      int y = (screenSize.height-pg.getHeight())/2;
      pg.setLocation(x,y);
      pg.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
      pg.setVisible(true);
      while(PropertyGUI.f);
     // pg.setEnabled(false);
      pg.setVisible(false);
      //GUI结束=============================================GUI结束

//找到选中的指针，进行提取相应的d  和  r；=======================================================选中相应的指针进行单独提取，把选中的指针提取出来给ps========
      FileReader fr=new FileReader("D:\\property\\propositions.txt");
      assert fr!=null;
      BufferedReader br=new BufferedReader(fr);
      String ps="";
      String s;
      while((s=br.readLine())!=null){
          ps=ps+s;
         // System.out.println(ps);
      }
      br.close();
      String var=ps.substring(ps.indexOf("=>")+2,ps.indexOf("< length"));
     /*String pppp=ps.substring(ps.indexOf("r=>")).trim();
     String ppp=pppp.substring(pppp.indexOf("==")+2).trim();
     String pp=ppp.substring(ppp.indexOf("::")+2).trim();*/
      //四种形式propositions {!r,d,r,!d}=====(!r, !(blkNum==blkNum))=DecodeDataMerge, (d, blkNum!=0)=DecodeDataMerge, (r, blkNum==blkNum)=DecodeDataMerge, (!d, !(blkNum!=0))=DecodeDataMerge}
      Proposition proposition=new Proposition(ps);
      //String maps="";
      //List<Pair<String,String>> l=new ArrayList<>();
      //Iterator<String> it1=propositionsMap.keySet().iterator();
     // while(it1.hasNext()){


      //建立reachedSet======================================================建立reachedSet
        reached = factory.createReachedSet();
        //maps=it1.next();
        //maps=propositionsMap.get(maps).getFirst()+"&&"+propositionsMap.get(maps).getSecond();
        //Proposition proposition=new Proposition(maps);
        if (runCBMCasExternalTool) {
          algorithm = new ExternalCBMCAlgorithm(filename, config, logger);

        } else {
          //CFA cfa = parse(filename, stats);//parsing the function.170
          GlobalInfo.getInstance().storeCFA(cfa);
          stopIfNecessary();

          ConfigurableProgramAnalysis cpa = factory.createCPA(cfa, stats);

          algorithm = factory.createAlgorithm(cpa, filename, cfa, stats);
          myCpa=new MyCPA(config,logger,cpa);
          //运行自己的方法=========================================================run1方法
            MyCPA.run1(reached,proposition);
          if (algorithm instanceof ImpactAlgorithm) {
            ImpactAlgorithm mcmillan = (ImpactAlgorithm)algorithm;//see1
            reached.add(mcmillan.getInitialState(cfa.getMainFunction()), mcmillan.getInitialPrecision(cfa.getMainFunction()));
          } else {
            //初始化reachedSet================================================================初始化
            initializeReachedSet(reached, cpa, cfa.getMainFunction());//seeing
          }
        }


        //mycode
        if(myCpa!=null)
        errorState=myCpa.run(reached,proposition);
        //mycodeend
        printConfigurationWarnings();

        stats.creationTime.stop();
        stopIfNecessary();
        // now everything necessary has been instantiated
        if (disableAnalysis) {
          return new CPAcheckerResult(Result.NOT_YET_STARTED, null, null);
        }

        // run analysis
        result = Result.UNKNOWN; // set to unknown so that the result is correct in case of exception
        //mycode
        boolean isComplete =true;//runAlgorithm(algorithm, reached, stats);//see in the next

        System.out.println("结合大小:"+reached.size());
       /* System.out.println("***************输出CFA*******************");
        ImmutableSortedSet<CFANode> all=(ImmutableSortedSet<CFANode>) cfa.getAllNodes();
        Iterator<CFANode> it=all.iterator();
        while(it.hasNext()){
          CFANode cn=it.next();
          System.out.println(cn.toString()+"-->"+cn.cfaPrecision);
        }
        */
        //result = analyzeResult(reached, isComplete);
        result=reached.getResult();
        //l.add(Pair.of(maps,result.toString()));
      //}
      System.out.println("*************结果**********");
      writeFile(filename,var,result,errorState);
      TxtToXml ttx=new TxtToXml();
      ttx.createXml();

      //for(Pair pp:l){
      //  if(pp.getSecond().equals("UNSAFE"))
      //   System.out.println(pp);
      //}
     /* FileReader fr=new FileReader("D:\\property\\propositions.txt");
      assert fr!=null;
      BufferedReader br=new BufferedReader(fr);
      String ps="";
      String s;
      while((s=br.readLine())!=null){
          ps=ps+s;
         // System.out.println(ps);
      }
      br.close();
      Proposition proposition=new Proposition(ps);
      if (runCBMCasExternalTool) {
        algorithm = new ExternalCBMCAlgorithm(filename, config, logger);

      } else {
        //CFA cfa = parse(filename, stats);//parsing the function.170
        GlobalInfo.getInstance().storeCFA(cfa);
        stopIfNecessary();

        ConfigurableProgramAnalysis cpa = factory.createCPA(cfa, stats);

        algorithm = factory.createAlgorithm(cpa, filename, cfa, stats);
        myCpa=new MyCPA(config,logger,cpa);
        myCpa.run1(reached,proposition);
        if (algorithm instanceof ImpactAlgorithm) {
          ImpactAlgorithm mcmillan = (ImpactAlgorithm)algorithm;//see1
          reached.add(mcmillan.getInitialState(cfa.getMainFunction()), mcmillan.getInitialPrecision(cfa.getMainFunction()));
        } else {
          initializeReachedSet(reached, cpa, cfa.getMainFunction());//seeing
        }
      }


      //mycode
      if(myCpa!=null)
        myCpa.run(reached,proposition);
      //mycodeend
      printConfigurationWarnings();

      stats.creationTime.stop();
      stopIfNecessary();
      // now everything necessary has been instantiated
      if (disableAnalysis) {
        return new CPAcheckerResult(Result.NOT_YET_STARTED, null, null);
      }

      // run analysis
      result = Result.UNKNOWN; // set to unknown so that the result is correct in case of exception
      //mycode
      boolean isComplete =true;//runAlgorithm(algorithm, reached, stats);//see in the next

      System.out.println("结合大小:"+reached.size());
     /* System.out.println("***************输出CFA*******************");
      ImmutableSortedSet<CFANode> all=(ImmutableSortedSet<CFANode>) cfa.getAllNodes();
      Iterator<CFANode> it=all.iterator();
      while(it.hasNext()){
        CFANode cn=it.next();
        System.out.println(cn.toString()+"-->"+cn.cfaPrecision);
      }
      */
      //result = analyzeResult(reached, isComplete);
      //result=reached.getResult();//mycode
    } catch (IOException e) {
      logger.logUserException(Level.SEVERE, e, "Could not read file");

    } catch (ParserException e) {
      // only log message, not whole exception because this is a C problem,
      // not a CPAchecker problem
      logger.logUserException(Level.SEVERE, e, "Parsing failed");
      logger.log(Level.INFO, "Make sure that the code was preprocessed using Cil (HowTo.txt).\n"
          + "If the error still occurs, please send this error message together with the input file to cpachecker-users@sosy-lab.org.");

    } catch (InvalidConfigurationException e) {
      logger.logUserException(Level.SEVERE, e, "Invalid configuration");

    } catch (InterruptedException e) {
      // CPAchecker must exit because it was asked to
      // we return normally instead of propagating the exception
      // so we can return the partial result we have so far

    } catch (CPAException e) {
      logger.logUserException(Level.SEVERE, e, null);
    }
    return new CPAcheckerResult(result, reached, stats);
  }



  private void extractPropositions(CFA cfa, Map<String, Pair<String, String>> propositionsMap) {
    // TODO Auto-generated method stub
    Iterator<CFANode> iterator=cfa.getAllNodes().iterator();
    int j=1;
    while(iterator.hasNext()){
      CFANode next=iterator.next();
      List<CFAEdge> edges=next.getLeavingEdge();
      for(CFAEdge edge:edges){
        //functionCall=========================================龙1
        if(edge instanceof CFunctionCallEdge){
         List<Integer> types=new ArrayList<Integer>();
         List<String>  vars=new ArrayList<String>();
         List<CExpression> fc=((CFunctionCallEdge)(edge)).getArguments();
         for(CExpression e:fc){
           CType type=e.getExpressionType();
           if(type instanceof CPointerType)
              types.add(1);
           else
              types.add(0);
         }
         CFANode suc=edge.getSuccessor();
         if(suc instanceof CFunctionEntryNode){
           vars=((CFunctionEntryNode) suc).getFunctionParameterNames();
         }
         for(int i=0;i<types.size()&&vars.size()==types.size();i++){
           if(types.get(i)==1){
             String function=suc.getFunctionName();
             String var=function+"::"+vars.get(i);
             String first="d=>"+var+" != 0";
             String second="r=>"+var+" == "+var;
             propositionsMap.put(var,Pair.of(first, second));
           }
         }
        }
        //其他声明语句================================================龙2
        else if(edge instanceof CDeclarationEdge){
          CDeclaration declaration=((CDeclarationEdge) edge).getDeclaration();
          if(declaration instanceof CVariableDeclaration){
            String function="";
            String var=declaration.getName();
            CType type=declaration.getType();
            if(declaration.isGlobal()){
              function="Global";
            }
            else{
              function=next.getFunctionName();
            }
            if(type instanceof CPointerType){
              String basicType=((CPointerType) type).toASTString(var);
             // System.out.println("basicType="+basicType);
              var=function+"::"+var;
              String first="d=>"+var+" != 0";
              String second="r=>"+var+" == "+var;
              propositionsMap.put(var,Pair.of(first, second));
            }
          }
        }
      }
    }
  }

  private void long_extractPropositions(CFA cfa, Map<String, Pair<String, String>> propositionsMap) {
    // TODO Auto-generated method stub
    Iterator<CFANode> iterator=cfa.getAllNodes().iterator();
    int j=1;
    while(iterator.hasNext()){
      CFANode next=iterator.next();
      List<CFAEdge> edges=next.getLeavingEdge();


      for(CFAEdge edge:edges){//对所有CFANode的leavingEdge进行遍历

        if(edge instanceof CFunctionCallEdge){//===================================1.CFunctionCallEdge
         List<Integer> types=new ArrayList<Integer>();
         List<String>  vars=new ArrayList<String>();
         List<CExpression> fc=((CFunctionCallEdge)(edge)).getArguments();
         for(CExpression e:fc){
           CType type=e.getExpressionType();
           if(type instanceof CPointerType)
              types.add(1);
           else
              types.add(0);
         }
         CFANode suc=edge.getSuccessor();
         if(suc instanceof CFunctionEntryNode){
           vars=((CFunctionEntryNode) suc).getFunctionParameterNames();
         }
         for(int i=0;i<types.size()&&vars.size()==types.size();i++){
           if(types.get(i)==1){
             String function=suc.getFunctionName();
             String var=function+"::"+vars.get(i);
             String first="d=>"+var+" != 0";
             String second="r=>"+var+" == "+var;
             propositionsMap.put(var,Pair.of(first, second));
           }
         }
        }
        else if(edge instanceof CDeclarationEdge){//==================================2.CDeclarationEdge
          CDeclaration declaration=((CDeclarationEdge) edge).getDeclaration();
          if(declaration instanceof CVariableDeclaration){
            String function="";
            String var=declaration.getName();
            CType type=declaration.getType();
            if(declaration.isGlobal()){
              function="Global";
            }else{
              function=next.getFunctionName();
            }
            if(type instanceof CPointerType){
              String basicType=((CPointerType) type).toASTString(var);
             // System.out.println("basicType="+basicType);
              var=function+"::"+var;
              String first="d=>"+var+" != 0";
              String second="r=>"+var+" == "+var;
              propositionsMap.put(var,Pair.of(first, second));
            }
          }
        }
      }
    }
  }


  private CFA parse(String filename, MainCPAStatistics stats) throws InvalidConfigurationException, IOException,
      ParserException, InterruptedException {
    // parse file and create CFA
    CFACreator cfaCreator = new CFACreator(config,logger);
    stats.setCFACreator(cfaCreator);

    return cfaCreator.parseFileAndCreateCFA(filename);
  }

  private void printConfigurationWarnings() {
    Set<String> unusedProperties = config.getUnusedProperties();
    if (!unusedProperties.isEmpty()) {
      logger.log(Level.WARNING, "The following configuration options were specified but are not used:\n",
          Joiner.on("\n ").join(unusedProperties), "\n");
    }
    Set<String> deprecatedProperties = config.getDeprecatedProperties();
    if (!deprecatedProperties.isEmpty()) {
      logger.log(Level.WARNING, "The following options are deprecated and will be removed in the future:\n",
          Joiner.on("\n ").join(deprecatedProperties), "\n");
    }
  }

  private boolean runAlgorithm(final Algorithm algorithm,              ////see6
      ReachedSet reached,
      final MainCPAStatistics stats) throws CPAException, InterruptedException {

    logger.log(Level.INFO, "Starting analysis ...");
    System.out.println("大"+algorithm.getClass().toString());
    boolean isComplete = true;

    // register management interface for CPAchecker
    CPAcheckerBean mxbean = new CPAcheckerBean(reached, logger);

    stats.analysisTime.start();
    try {

      do {
        if(algorithm instanceof CPAAlgorithm){
         isComplete &= ((CPAAlgorithm)algorithm).run(reached);
        }
        else{
          isComplete &= algorithm.run(reached);//q1
        }
        System.out.println("CPAChecker.reachedSet="+reached.size());
        // either run only once (if stopAfterError == true)
        // or until the waitlist is empty
      } while (!stopAfterError && reached.hasWaitingState());

      logger.log(Level.INFO, "Stopping analysis ...");
      return isComplete;

    } finally {
      stats.analysisTime.stop();
      stats.programTime.stop();
     System.out.println("ok!");
     Runtime rt=Runtime.getRuntime();
     System.out.println("内存:"+(rt.totalMemory() - rt.freeMemory()));
      // unregister management interface for CPAchecker
      mxbean.unregister();
    }
  }

  private Result analyzeResult1(ReachedSet reached, boolean isComplete) {
    if(reached.getResult()==Result.UNSAFE)
       return Result.UNSAFE;
    return Result.SAFE;
  }
  private Result analyzeResult(ReachedSet reached, boolean isComplete) {
    /*if(((DefaultReachedSet)reached).safe){
      System.out.println("Verification result:Safe");
      return Result.SAFE;
    }
    else{
      System.out.println("Verification result:UnSafe");
      return Result.UNSAFE;
    }*/
    if (from(reached).anyMatch(IS_TARGET_STATE)) {
      return Result.UNSAFE;
    }

    if (reached.hasWaitingState()) {
      logger.log(Level.WARNING, "Analysis not completed: there are still states to be processed.");
      return Result.UNKNOWN;
    }

    if (!isComplete) {
      logger.log(Level.WARNING, "Analysis incomplete: no errors found, but not everything could be checked.");
      return Result.UNKNOWN;
    }

    return Result.SAFE;
  }
  private void writeFile(String filename,String var, Result result, Pair<ARGState, ARGState> errorState) throws IOException {
    // TODO Auto-generated method stub
    FileOutputStream fr=new FileOutputStream("D:\\camc\\XML\\array\\result.txt",true);
    assert fr!=null;
    BufferedOutputStream br=new BufferedOutputStream(fr);
    CFAEdge errorEdge=null;
    StringBuilder str=new StringBuilder();
    str.append(filename+"<->");
    str.append(var+"<->");
    str.append(result.toString()+"<->");
    if(errorState!=null){
      errorEdge=errorState.getFirst().getEdgeToChild(errorState.getSecond());
      str.append("Line "+errorEdge.getLineNumber()+errorEdge.getDescription().replaceAll("\n", " ").replace('"', '\''));
    }
    else{
      str.append("null");
    }
    str.append("\r\n");
    br.write(str.toString().getBytes());
    br.close();
    fr.close();
  }
  private void initializeReachedSet(
      final ReachedSet reached,
      final ConfigurableProgramAnalysis cpa,
      final FunctionEntryNode mainFunction) {
    logger.log(Level.FINE, "Creating initial reached set");
    AbstractState initialState = cpa.getInitialState(mainFunction);//q2
    Precision initialPrecision = cpa.getInitialPrecision(mainFunction);

    reached.add(initialState, initialPrecision);
  }
}
