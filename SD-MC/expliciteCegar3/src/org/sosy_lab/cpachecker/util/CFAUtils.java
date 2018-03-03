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
package org.sosy_lab.cpachecker.util;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializer;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.core.CPAchecker;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.xidian.crl.CRLGlobal;

import com.google.common.base.Function;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedSet;
import com.google.common.collect.Sets;
import com.google.common.collect.UnmodifiableIterator;

public class CFAUtils {

  /**
   * Return an {@link Iterable} that contains all entering edges of a given CFANode,
   * including the summary edge if the node as one.
   */
  public static List<Pair<String,String>> subTwoLens=new ArrayList<Pair<String,String>>();
  public static FluentIterable<CFAEdge> allEnteringEdges(final CFANode node) {
    checkNotNull(node);
    return new FluentIterable<CFAEdge>() {

      @Override
      public Iterator<CFAEdge> iterator() {
        return new UnmodifiableIterator<CFAEdge>() {

          // the index of the next edge (-1 means the summary edge)
          private int i = (node.getEnteringSummaryEdge() != null) ? -1 : 0;

          @Override
          public boolean hasNext() {
            return i < node.getNumEnteringEdges();
          }

          @Override
          public CFAEdge next() {
            if (i == -1) {
              i = 0;
              return node.getEnteringSummaryEdge();
            }
            return node.getEnteringEdge(i++);
          }
        };
      }
    };
  }

  /**
   * Return an {@link Iterable} that contains the entering edges of a given CFANode,
   * excluding the summary edge.
   */
  public static FluentIterable<CFAEdge> enteringEdges(final CFANode node) {
    checkNotNull(node);
    return new FluentIterable<CFAEdge>() {

      @Override
      public Iterator<CFAEdge> iterator() {
        return new UnmodifiableIterator<CFAEdge>() {

          // the index of the next edge
          private int i = 0;

          @Override
          public boolean hasNext() {
            return i < node.getNumEnteringEdges();
          }

          @Override
          public CFAEdge next() {
             return node.getEnteringEdge(i++);
          }
        };
      }
    };
  }

  /**
   * Return an {@link Iterable} that contains all leaving edges of a given CFANode,
   * including the summary edge if the node as one.
   */
  public static FluentIterable<CFAEdge> allLeavingEdges(final CFANode node) {
    checkNotNull(node);
    return new FluentIterable<CFAEdge>() {

      @Override
      public Iterator<CFAEdge> iterator() {
        return new UnmodifiableIterator<CFAEdge>() {

          // the index of the next edge (-1 means the summary edge)
          private int i = (node.getLeavingSummaryEdge() != null) ? -1 : 0;

          @Override
          public boolean hasNext() {
            return i < node.getNumLeavingEdges();
          }

          @Override
          public CFAEdge next() {
            if (i == -1) {
              i = 0;
              return node.getLeavingSummaryEdge();
            }
            return node.getLeavingEdge(i++);
          }
        };
      }
    };
  }

  /**
   * Return an {@link Iterable} that contains the leaving edges of a given CFANode,
   * excluding the summary edge.
   */
  public static FluentIterable<CFAEdge> leavingEdges(final CFANode node) {
    checkNotNull(node);
    return new FluentIterable<CFAEdge>() {

      @Override
      public Iterator<CFAEdge> iterator() {
        return new UnmodifiableIterator<CFAEdge>() {

          // the index of the next edge
          private int i = 0;

          @Override
          public boolean hasNext() {
            return i < node.getNumLeavingEdges();
          }

          @Override
          public CFAEdge next() {
             return node.getLeavingEdge(i++);
          }
        };
      }
    };
  }

  private static final Function<CFAEdge,  CFANode> TO_PREDECESSOR = new Function<CFAEdge,  CFANode>() {
      @Override
      public CFANode apply(CFAEdge pInput) {
        return pInput.getPredecessor();
      }
    };


  private static final Function<CFAEdge,  CFANode> TO_SUCCESSOR = new Function<CFAEdge,  CFANode>() {
    @Override
    public CFANode apply(CFAEdge pInput) {
      return pInput.getSuccessor();
    }
  };

  /**
   * Return an {@link Iterable} that contains the predecessor nodes of a given CFANode,
   * excluding the one reachable via the summary edge (if there is one).
   */
  public static FluentIterable<CFANode> predecessorsOf(final CFANode node) {
    return enteringEdges(node).transform(TO_PREDECESSOR);
  }

  /**
   * Return an {@link Iterable} that contains all the predecessor nodes of a given CFANode,
   * including the one reachable via the summary edge (if there is one).
   */
  public static FluentIterable<CFANode> allPredecessorsOf(final CFANode node) {
    return allEnteringEdges(node).transform(TO_PREDECESSOR);
  }

  /**
   * Return an {@link Iterable} that contains the successor nodes of a given CFANode,
   * excluding the one reachable via the summary edge (if there is one).
   */
  public static FluentIterable<CFANode> successorsOf(final CFANode node) {
    return leavingEdges(node).transform(TO_SUCCESSOR);
  }

  /**
   * Return an {@link Iterable} that contains all the successor nodes of a given CFANode,
   * including the one reachable via the summary edge (if there is one).
   */
  public static FluentIterable<CFANode> allSuccessorsOf(final CFANode node) {
    return allLeavingEdges(node).transform(TO_SUCCESSOR);
  }

  // wrapper class for Set<CFANode> because Java arrays don't like generics
  private static class Edge {
    private final Set<CFANode> nodes = new HashSet<CFANode>(1);

    private void add(Edge n) {
      nodes.addAll(n.nodes);
    }

    private void add(CFANode n) {
      nodes.add(n);
    }

    private Set<CFANode> asNodeSet() {
      return nodes;
    }
  }

  public static class Loop {

    // loopHeads is a sub-set of nodes such that all infinite paths through
    // the set nodes will pass through at least one node in loopHeads infinitively often
    // i.e. you will have to pass through at least one loop head in every iteration
    private ImmutableSet<CFANode> loopHeads;

    private ImmutableSortedSet<CFANode> nodes;

    // the following sets are computed lazily by calling {@link #computeSets()}
    private ImmutableSet<CFAEdge> innerLoopEdges;
    private ImmutableSet<CFAEdge> incomingEdges;
    private ImmutableSet<CFAEdge> outgoingEdges;

    public Loop(CFANode loopHead, Set<CFANode> pNodes) {
      loopHeads = ImmutableSet.of(loopHead);
      nodes = ImmutableSortedSet.<CFANode>naturalOrder()
                                .addAll(pNodes)
                                .add(loopHead)
                                .build();
    }

    private void computeSets() {
      if (innerLoopEdges != null) {
        assert incomingEdges != null;
        assert outgoingEdges != null;
      }

      Set<CFAEdge> incomingEdges = new HashSet<CFAEdge>();
      Set<CFAEdge> outgoingEdges = new HashSet<CFAEdge>();

      for (CFANode n : nodes) {
        for (int i = 0; i < n.getNumEnteringEdges(); i++) {
          incomingEdges.add(n.getEnteringEdge(i));
        }
        for (int i = 0; i < n.getNumLeavingEdges(); i++) {
          outgoingEdges.add(n.getLeavingEdge(i));
        }
      }

      innerLoopEdges = Sets.intersection(incomingEdges, outgoingEdges).immutableCopy();
      incomingEdges.removeAll(innerLoopEdges);
      outgoingEdges.removeAll(innerLoopEdges);

      assert !incomingEdges.isEmpty() : "Unreachable loop?";

      this.incomingEdges = ImmutableSet.copyOf(incomingEdges);
      this.outgoingEdges = ImmutableSet.copyOf(outgoingEdges);
    }

    void addNodes(Loop l) {
      nodes = ImmutableSortedSet.<CFANode>naturalOrder()
                                .addAll(nodes)
                                .addAll(l.nodes)
                                .build();

      innerLoopEdges = null;
      incomingEdges = null;
      outgoingEdges = null;
    }

    void mergeWith(Loop l) {
      loopHeads = Sets.union(loopHeads, l.loopHeads).immutableCopy();
      addNodes(l);
    }

    public boolean intersectsWith(Loop l) {
      return !Sets.intersection(nodes, l.nodes).isEmpty();
    }

    /**
     * Check if this loop is an outer loop of another, given one.
     */
    public boolean isOuterLoopOf(Loop other) {
      this.computeSets();
      other.computeSets();

      return this.innerLoopEdges.containsAll(other.incomingEdges)
          && this.innerLoopEdges.containsAll(other.outgoingEdges);
    }

    public ImmutableSortedSet<CFANode> getLoopNodes() {
      return nodes;
    }

    public ImmutableSet<CFANode> getLoopHeads() {
      return loopHeads;
    }

    public ImmutableSet<CFAEdge> getIncomingEdges() {
      computeSets();
      return incomingEdges;
    }

    public ImmutableSet<CFAEdge> getOutgoingEdges() {
      computeSets();
      return outgoingEdges;
    }

    @Override
    public String toString() {
      computeSets();
      return "Loop with heads " + loopHeads + "\n"
           + "  incoming: " + incomingEdges + "\n"
           + "  outgoing: " + outgoingEdges + "\n"
           + "  nodes:    " + nodes;
    }
  }

  public static Collection<Loop> findLoops(SortedSet<CFANode> nodes) throws ParserException {
    final int min = nodes.first().getNodeNumber();
    final int max = nodes.last().getNodeNumber();
    final int size = max + 1 - min;

    nodes = new TreeSet<CFANode>(nodes); // copy nodes because we change it

    // all nodes of the graph
    // Fields may be null, iff there is no node with this number.
    // forall i : nodes[i].getNodeNumber() == i + min
    final CFANode[] nodesArray = new CFANode[size];

    // all edges of the graph
    // Iff there is an edge from nodes[i] to nodes[j], edges[i][j] is not null.
    // The set edges[i][j].nodes contains all nodes that were eliminated and merged into this edge.
    final Edge[][] edges =  new Edge[size][size];

    // FIRST step: initialize arrays
    for (CFANode n : nodes) {
      int i = n.getNodeNumber() - min;
      assert nodesArray[i] == null;
      nodesArray[i] = n;

      for (int e = 0; e < n.getNumLeavingEdges(); e++) {
        CFAEdge edge = n.getLeavingEdge(e);
        CFANode succ = edge.getSuccessor();
        int j = succ.getNodeNumber() - min;
        edges[i][j] = new Edge();
      }
    }

    // SECOND step: simplify graph and identify loops
    List<Loop> loops = new ArrayList<Loop>();
    boolean changed;
    do {
      // first try without the "reverse merge" strategy
      // this strategy may eliminate real loop heads too early so that the
      // algorithm would propose another node of the loop has loop head
      // (which is counter-intuitive to the user)
      changed = identifyLoops(false, nodes, min, nodesArray, edges, loops);

      if (!changed && !nodes.isEmpty()) {
        // but if we have to, try and use this strategy
        changed = identifyLoops(true, nodes, min, nodesArray, edges, loops);
      }

    } while (changed && !nodes.isEmpty()); // stop if nothing has changed or nodes is empty


    // check that the complete graph has collapsed
    if (!nodes.isEmpty()) {
      throw new ParserException("Code structure is too complex, could not detect all loops!");
    }

    // THIRD step:
    // check all pairs of loops if one is an inner loop of the other
    // the check is symmetric, so we need to check only (i1, i2) with i1 < i2

    NavigableSet<Integer> toRemove = new TreeSet<Integer>();
    for (int i1 = 0; i1 < loops.size(); i1++) {
      Loop l1 = loops.get(i1);

      for (int i2 = i1+1; i2 < loops.size(); i2++) {
        Loop l2 = loops.get(i2);

        if (!l1.intersectsWith(l2)) {
          // loops have nothing in common
          continue;
        }

        if (l1.isOuterLoopOf(l2)) {

          // l2 is an inner loop
          // add it's nodes to l1
          l1.addNodes(l2);

        } else if (l2.isOuterLoopOf(l1)) {

          // l1 is an inner loop
          // add it's nodes to l2
          l2.addNodes(l1);

        } else {
          // strange goto loop, merge the two together

          l1.mergeWith(l2);
          toRemove.add(i2);
        }
      }
    }

    for (int i : toRemove.descendingSet()) { // need to iterate in reverse order!
      loops.remove(i);
    }

    return loops;
  }

  private static boolean identifyLoops(boolean reverseMerge, SortedSet<CFANode> nodes, final int offset,
      final CFANode[] nodesArray, final Edge[][] edges, List<Loop> loops) {

    final int size = edges.length;

    boolean changed = false;

      // merge nodes with their neighbors, if possible
      Iterator<CFANode> it = nodes.iterator();
      while (it.hasNext()) {
        final CFANode currentNode = it.next();
        final int current = currentNode.getNodeNumber() - offset;

        // find edges of current
        final int predecessor = findSingleIncomingEdgeOfNode(current, edges);
        final int successor   = findSingleOutgoingEdgeOfNode(current, edges);

        if ((predecessor == -1) && (successor == -1)) {
          // no edges, eliminate node
          it.remove(); // delete currentNode

        } else if ((predecessor == -1) && (successor > -1)) {
          // no incoming edges, one outgoing edge
          final int successor2 = findSingleOutgoingEdgeOfNode(successor, edges);
          if (successor2 == -1) {
            // the current node is a source that is only connected with a sink
            // we can remove it
            edges[current][successor] = null;
            it.remove(); // delete currentNode
          }

        } else if ((successor == -1) && (predecessor > -1)) {
          // one incoming edge, no outgoing edges
          final int predecessor2 = findSingleIncomingEdgeOfNode(predecessor, edges);
          if (predecessor2 == -1) {
            // the current node is a sink that is only connected with a source
            // we can remove it
            edges[predecessor][current] =  null;
            it.remove(); // delete currentNode
          }

        } else if ((predecessor > -1) && (successor != -1)) {
          // current has a single incoming edge from predecessor and is no sink, eliminate current
          changed = true;

          // copy all outgoing edges (current,j) to (predecessor,j)
          for (int j = 0; j < size; j++) {
            if (edges[current][j] != null) {
              // combine three edges (predecessor,current) (current,j) and (predecessor,j)
              // into a single edge (predecessor,j)
              Edge targetEdge = getEdge(predecessor, j, edges);
              targetEdge.add(edges[predecessor][current]);
              targetEdge.add(edges[current][j]);
              targetEdge.add(currentNode);
              edges[current][j] = null;
            }
          }

          // delete from graph
          edges[predecessor][current] = null;
          it.remove(); // delete currentNode

          // now predecessor node might have gained a self-edge
          if (edges[predecessor][predecessor] != null) {
            CFANode pred = nodesArray[predecessor];
            handleLoop(pred, predecessor, edges, loops);
          }


        } else if (reverseMerge && (successor > -1) && (predecessor != -1)) {
          // current has a single outgoing edge to successor and is no source, eliminate current
          changed = true;

          // copy all incoming edges (j,current) to (j,successor)
          for (int j = 0; j < size; j++) {
            if (edges[j][current] != null) {
              // combine three edges (j,current) (current,successor) and (j,successor)
              // into a single edge (j,successor)
              Edge targetEdge = getEdge(j, successor, edges);
              targetEdge.add(edges[j][current]);
              targetEdge.add(edges[current][successor]);
              targetEdge.add(currentNode);
              edges[j][current] = null;
            }
          }

          // delete from graph
          edges[current][successor] = null;
          it.remove(); // delete currentNode

          // now successor node might have gained a self-edge
          if (edges[successor][successor] != null) {
            CFANode succ = nodesArray[successor];
            handleLoop(succ, successor, edges, loops);
          }
        }
      }

      return changed;
  }

  // get edge from edges array, ensuring that it is added if it does not exist yet
  private static Edge getEdge(int i, int j, Edge[][] edges) {
    Edge result = edges[i][j];
    if (edges[i][j] == null) {
      result = new Edge();
      edges[i][j] = result;
    }
    return result;
  }

  // create a loop from a node with a self-edge
  private static void handleLoop(final CFANode loopHead, int loopHeadIndex,
      final Edge[][] edges, Collection<Loop> loops) {
    assert loopHead != null;

    // store loop
    Loop loop = new Loop(loopHead, edges[loopHeadIndex][loopHeadIndex].asNodeSet());
    loops.add(loop);

    // remove this loop from the graph
    edges[loopHeadIndex][loopHeadIndex] = null;
  }

  // find index of single predecessor of node i
  // if there is no successor, -1 is returned
  // if there are several successor, -2 is returned
  private static int findSingleIncomingEdgeOfNode(int i, Edge[][] edges) {
    final int size = edges.length;

    int predecessor = -1;
    for (int j = 0; j < size; j++) {
      if (edges[j][i] != null) {
        // i has incoming edge from j

        if (predecessor > -1) {
          // not the only incoming edge
          return -2;
        } else {
          predecessor = j;
        }
      }
    }
    return predecessor;
  }

  // find index of single successor of node i
  // if there is no successor, -1 is returned
  // if there are several successors, -2 is returned
  private static int findSingleOutgoingEdgeOfNode(int i, Edge[][] edges) {
    final int size = edges.length;

    int successor = -1;
    for (int j = 0; j < size; j++) {
      if (edges[i][j] != null) {
        // i has outgoing edge to j

        if (successor > -1) {
          // not the only outgoing edge
          return -2;
        } else {
          successor = j;
        }
      }
    }
    return successor;
  }
  public static boolean judge(CFAEdge edge,String var) {
    // TODO Auto-generated method stub
      if(edge instanceof CStatementEdge){//如：i=0等
          CStatement statement= ((CStatementEdge) edge).getStatement();
          if(statement instanceof CExpressionAssignmentStatement){
            CExpression leftSide=((CExpressionAssignmentStatement) statement).getLeftHandSide();
            CExpression rightSide=((CExpressionAssignmentStatement) statement).getRightHandSide();
            boolean result=leftSide.judge(var,false);
            return result?result:rightSide.judge(var,false);
          }
          else if(statement instanceof CExpressionStatement){
            CExpression exp=((CExpressionStatement) statement).getExpression();
            return exp.judge(var,false);
          }
      }
      else if(edge instanceof CAssumeEdge){//如!(i<2)等
        CExpression exp=((CAssumeEdge) edge).getExpression();
        return exp.judge(var,false);
      }
      else if(edge instanceof CDeclarationEdge){//如：int i；等
          CDeclaration declaration=((CDeclarationEdge) edge).getDeclaration();
          if(declaration instanceof CVariableDeclaration){
            CInitializer init= ((CVariableDeclaration) declaration).getInitializer();
            if(init!=null&&init instanceof CInitializerExpression){
              CExpression exp=((CInitializerExpression) init).getExpression();
              return exp.judge(var,false);
            }
          }
      }
      else if(edge instanceof CReturnStatementEdge){
          CExpression exp=((CReturnStatementEdge)edge).getExpression();
          if(exp!=null)
           return exp.judge(var,false);
      }
      else if(edge instanceof CFunctionCallEdge){
          CFunctionCall call=((CFunctionCallEdge)edge).getFunctionCall();
          if(call instanceof CFunctionCallAssignmentStatement){
            CExpression leftSide=((CFunctionCallAssignmentStatement) call).getLeftHandSide();
            CFunctionCallExpression rightSide=((CFunctionCallAssignmentStatement) call).getRightHandSide();
            assert leftSide!=null && rightSide!=null;
            boolean result=leftSide.judge(var,false);
            return result?result:rightSide.judge(var,false);
          }
          else if(call instanceof CFunctionCallStatement){
            CFunctionCallExpression ce=((CFunctionCallStatement) call).getFunctionCallExpression();
            return ce.judge(var,false);
          }
      }
      else if(edge instanceof CFunctionSummaryEdge){
        CFunctionCall call=((CFunctionSummaryEdge)edge).getExpression();
        if(call instanceof CFunctionCallAssignmentStatement){
          CExpression leftSide=((CFunctionCallAssignmentStatement) call).getLeftHandSide();
          CFunctionCallExpression rightSide=((CFunctionCallAssignmentStatement) call).getRightHandSide();
          boolean result=leftSide.judge(var,false);
          return result?result:rightSide.judge(var,false);
        }
      }
      return false;
  }
//加入龙的judge方法===================================================================龙judge方法
  public static boolean long_judge(CFAEdge edge,String var){

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
    String funName= ps.substring(ps.indexOf("=>")+2, ps.indexOf("::")).trim();
   String fullVar=funName+"::"+var;
    //第一种情况=========最简单的判断a[*]形式=======有的话就返回true

    String edgeStr=edge.toString();



    edgeStr=edgeStr.replaceAll(" ", "");
    String aaname=var;

    var=var.replaceAll("\\*", "\\\\*");
    var=var.replaceAll("\\.", "\\\\.");
    var=var.replaceAll("\\(", "\\\\(");
    var=var.replaceAll("\\)", "\\\\)");
    var=var.replaceAll("\\[", "\\\\[");
    var=var.replaceAll("\\]", "\\\\]");
    int temp=CRLGlobal.getInstance().getFunFlgLen();
    if(!(edge instanceof CDeclarationEdge)){


      //看是否是指针形式=======先看指针
      if(CPAchecker.nameToLen!=null&&CPAchecker.nameToLen.get(fullVar)!=null)
      if(CPAchecker.nameToLen.get(fullVar).equals("pointer_array")){
      if(CRLGlobal.getInstance().getPointerArrFullLen()=="noPointerArrLen"){
        return false;
      }else if(edgeStr.matches(".*"+"\\*"+"\\("+var+".*"+"\\)"+".*")||edgeStr.matches(".*"+"\\*"+"\\("+var+"\\)"+".*")||edgeStr.matches(".*"+"\\*"+var+".*")){

        return true;
      }
      }



    //二维数组处理==================二维数组
      else if((CPAchecker.nameToLen.get(fullVar).equals("two_array"))||(!CRLGlobal.getFuntwoarrflag().isEmpty())&&(CRLGlobal.getFuntwoarrflag().get(CRLGlobal.getFuntwoarrflag().size()-1))){
        boolean istwoflg=isTwoArr(edgeStr,aaname);
         if(istwoflg){
           return true;

         }else{
           return false;
         }

      }





      //一维数组====================一维数组
      else if(edgeStr.matches(".*\\("+var+"\\)\\[.*\\].*")||edgeStr.matches(".*"+var+"\\[.*\\].*")){
        return true;
      }else if(edgeStr.matches(".*"+"\\*"+"\\("+var+"\\+"+".*"+"\\)"+".*")){
        return true;
      }else{
        return false;
      }
    }

    //第二种情况==============指针指向数组===如p->a，下面用到*(p+1)
    //第三种情况==============数组这样用======*(a+1)

    return false;


  }
  public static boolean isTwoArr(String str,String arrayName){
    if(!str.contains(arrayName)){
      return false;
    } else {
      List<Pair<String, String>> mysubTwoLens = new ArrayList<Pair<String, String>>();

      Stack<Character> stack = new Stack<Character>();
      Map<Integer, Integer> map = new HashMap<Integer, Integer>();
      Map<Integer, String> map$ = new HashMap<Integer, String>();
      // ArrayList<Pair<String,String>>  myAllTwoSubs=new ArrayList<Pair<String,String>>();
      List<Integer> templeft = new ArrayList<Integer>();//储存'['的在字符串中位置
      List<Integer> templeft1 = new ArrayList<Integer>();//储存'('的在字符串中位置
      // String returnStr="no";
      stack.push('A');
      str = str.replaceAll(" ", "");
      if (arrayName.contains(".")) {
        arrayName = arrayName.replaceAll(arrayName, "(" + arrayName + ")");
        arrayName = arrayName.replaceAll("\\(", "\\\\(");
        arrayName = arrayName.replaceAll("\\)", "\\\\)");
        arrayName = arrayName.replaceAll("\\[", "\\\\[");
        arrayName = arrayName.replaceAll("\\]", "\\\\]");


        str = str.replaceAll(arrayName, "#");
      } else {
        str = str.replaceAll(arrayName, "#");
      }
      if (str.contains("*#")) {
        str = str.replaceAll("\\*\\#", "\\$");
      }
      if (str.contains("*(#)")) {
        str = str.replaceAll("\\*\\(\\#\\)", "\\$");
      }
      char[] arr = str.toCharArray();


      for (int k = 0; k < arr.length; k++) {
        char c = arr[k];
        Character temp = stack.pop();
        if (c == '$') {//处理$问题=====一开始先放到map$这个MAP中<位置k,"0">
          //subTwoLens.add(Pair.of("0", "0"));
          map$.put(k, "0");

        }
        if (temp == 'A') {
          stack.push(temp);
        }



        if (temp == '[' && c == ']') { // ===============================总1
          List<Integer> tempRemOneArr = new ArrayList<Integer>();
          if ((templeft.get(templeft.size() - 1) - 3) >= 0) {
            if ((arr[templeft.get(templeft.size() - 1) - 1] == '#')
                || ((arr[templeft.get(templeft.size() - 1) - 1] == ')')
                    && (arr[templeft.get(templeft.size() - 1) - 2] == '#') && (arr[templeft.get(templeft.size() - 1) - 3] == '('))) {

              map.put(templeft.get(templeft.size() - 1), k);
              templeft.remove(templeft.size() - 1);

            } else if ((arr[templeft.get(templeft.size() - 1) - 1] == ']')) {

              for (Map.Entry<Integer, Integer> entry : map.entrySet()) {
                int i = entry.getKey();
                int j = entry.getValue();
                if (j == (templeft.get(templeft.size() - 1) - 1)) {
                  tempRemOneArr.add(i);
                  String firstLenStr = "(" + (String) str.subSequence(i + 1, j) + ")";
                  String secondLenStr = "(" + (String) str.subSequence(templeft.get(templeft.size() - 1) + 1, k) + ")";
                  subTwoLens.add(Pair.of(firstLenStr, secondLenStr));

                }

              }
            } else if ((arr[templeft.get(templeft.size() - 1) - 1] == ')')) {
              if (arr[templeft.get(templeft.size() - 1) - 2] == '$'
                  && arr[templeft.get(templeft.size() - 1) - 3] == '(') {//处理($)[0]此种形式====$问题
                int position$ = templeft.get(templeft.size() - 1) - 2;
                map$.remove(position$);
                String firstLenStr = "(0)";
                String secondLenStr = "(" + (String) str.subSequence(templeft.get(templeft.size() - 1) + 1, k) + ")";
                subTwoLens.add(Pair.of(firstLenStr, secondLenStr));
              } else {
                for (Map.Entry<Integer, Integer> entry : map.entrySet()) {
                  int i = entry.getKey();
                  int j = entry.getValue();
                  if (((templeft.get(templeft.size() - 1) - 2) >= 0) && (j == (templeft.get(templeft.size() - 1) - 2))) {//匹配，有(*(a+))此种形式
                    tempRemOneArr.add(i);
                    String firstLenStr = "(" + (String) str.subSequence(i, j) + ")";
                    String secondLenStr =
                        "(" + (String) str.subSequence(templeft.get(templeft.size() - 1) + 1, k) + ")";
                    subTwoLens.add(Pair.of(firstLenStr, secondLenStr));

                  }

                }
              }
            }
          } else if ((templeft.get(templeft.size() - 1) - 1) >= 0) {
            if ((arr[templeft.get(templeft.size() - 1) - 1] == '#')) {
              map.put(templeft.get(templeft.size() - 1), k);
              templeft.remove(templeft.size() - 1);

            } else if ((arr[templeft.get(templeft.size() - 1) - 1] == ']')) {

              for (Map.Entry<Integer, Integer> entry : map.entrySet()) {
                int i = entry.getKey();
                int j = entry.getValue();
                if (j == (templeft.get(templeft.size() - 1) - 1)) {
                  tempRemOneArr.add(i);
                  String firstLenStr = "(" + (String) str.subSequence(i + 1, j) + ")";
                  String secondLenStr = "(" + (String) str.subSequence(templeft.get(templeft.size() - 1) + 1, k) + ")";
                  subTwoLens.add(Pair.of(firstLenStr, secondLenStr));
                }
              }
            } else if ((arr[templeft.get(templeft.size() - 1) - 1] == ')')) {//不用处理$形式========因为[]必须前面-3得有值，因此在第一种情况中考虑即可

              for (Map.Entry<Integer, Integer> entry : map.entrySet()) {
                int i = entry.getKey();
                int j = entry.getValue();
                if (j == (templeft1.get(templeft1.size() - 1) - 1)) {//匹配，有*(a+)此种形式
                  tempRemOneArr.add(i);
                  String firstLenStr = "(" + (String) str.subSequence(i + 3, j) + ")";
                  String secondLenStr = "(" + (String) str.subSequence(templeft.get(templeft.size() - 1) + 1, k) + ")";
                  subTwoLens.add(Pair.of(firstLenStr, secondLenStr));

                }

              }
            }

          }
          if (!tempRemOneArr.isEmpty()) {
            for (int remi : tempRemOneArr) {
              map.remove(remi);
            }
          }




        }

        else if (temp == '(' && c == ')') {
          if (templeft1.get(templeft1.size() - 1) >= 1) {//考虑 ()左括号前面没东西
            if ((arr[templeft1.get(templeft1.size() - 1) - 1] == '*')
                && (arr[templeft1.get(templeft1.size() - 1) + 1] == '#')) {//一维数组处理

              map.put(templeft1.get(templeft1.size() - 1) + 3, k);

            } else if ((arr[templeft1.get(templeft1.size() - 1) - 1] == '*')
                && (arr[templeft1.get(templeft1.size() - 1) + 1] == '(')
                && (arr[templeft1.get(templeft1.size() - 1) + 2] == '*')) {//二维数组处理
              if (!map.isEmpty()) {
                int myfirstleftflag = templeft1.get(templeft1.size() - 1) + 6;
                int myfirstrightflag = map.get(myfirstleftflag);

                int secondleftflag = myfirstrightflag + 3;
                int secondrightflag = k;
                String firstLenStr = "(" + (String) str.subSequence(myfirstleftflag, myfirstrightflag) + ")";
                String secondLenStr = "(" + (String) str.subSequence(secondleftflag, secondrightflag) + ")";
                subTwoLens.add(Pair.of(firstLenStr, secondLenStr));
                map.remove(myfirstleftflag);//如果是二维数组，得去除一维数组中数据
              }
            } else if ((arr[templeft1.get(templeft1.size() - 1) - 1] == '*')
                && (arr[templeft1.get(templeft1.size() - 1) + 1] == '(')
                && (arr[templeft1.get(templeft1.size() - 1) + 2] == '$')) {//二维数组处理
              if (!map$.isEmpty()) {

                int secondleftflag = templeft1.get(templeft1.size() - 1) + 5;
                int secondrightflag = k;
                String firstLenStr = "(0)";
                String secondLenStr = "(" + (String) str.subSequence(secondleftflag, secondrightflag) + ")";
                subTwoLens.add(Pair.of(firstLenStr, secondLenStr));
                map$.remove(templeft1.get(templeft1.size() - 1) + 2);//如果是二维数组，得去除一维数组中数据
              }
            }

          }
          templeft1.remove(templeft1.size() - 1);

        } else if (temp == '[') {
          stack.push(temp);
        } else if (temp == '(')
          stack.push(temp);

        if (c == '[') {
          stack.push(c);
          templeft.add(k);



        }
        if (c == '(') {
          stack.push(c);
          templeft1.add(k);
        }



      }


      if (!subTwoLens.isEmpty()) { return true;

      }

      return false;
    }
  }
}

