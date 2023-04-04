/*
 * Copyright (c) 2013 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */
package com.ibm.wala.cast.js.callgraph.fieldbased;

import com.ibm.wala.cast.ir.ssa.AstIRFactory;
import com.ibm.wala.cast.ir.ssa.CAstBinaryOp;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.FlowGraph;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.FlowGraphBuilder;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.vertices.CallVertex;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.vertices.FuncVertex;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.vertices.VarVertex;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.vertices.Vertex;
import com.ibm.wala.cast.js.callgraph.fieldbased.flowgraph.vertices.VertexFactory;
import com.ibm.wala.cast.js.ipa.callgraph.JSAnalysisOptions;
import com.ibm.wala.cast.js.ssa.JavaScriptInvoke;
import com.ibm.wala.cast.js.types.JavaScriptMethods;
import com.ibm.wala.cast.types.AstMethodReference;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrike.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.IRFactory;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.cast.js.ipa.callgraph.JSSSAPropagationCallGraphBuilder;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.MonitorUtil;
import com.ibm.wala.util.MonitorUtil.IProgressMonitor;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Iterator2Iterable;
import com.ibm.wala.util.collections.MapUtil;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableMapping;
import com.ibm.wala.util.intset.MutableSharedBitVectorIntSet;
import com.ibm.wala.util.intset.OrdinalSetMapping;
import java.util.*;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import com.ibm.wala.ssa.SymbolTable;

import java.io.IOException;
import com.google.gson.Gson;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.charset.StandardCharsets;
import com.google.gson.reflect.TypeToken;


/**
 * Optimistic call graph builder that propagates inter-procedural data flow iteratively as call
 * edges are discovered. Slower, but potentially more sound than {@link
 * PessimisticCallGraphBuilder}.
 *
 * <p>This variant uses a worklist algorithm, generally making it scale better than {@link
 * OptimisticCallgraphBuilder}, which repeatedly runs the pessimistic algorithm.
 *
 * @author mschaefer
 */
public class WorklistBasedOptimisticCallgraphBuilder extends FieldBasedCallGraphBuilder {
  /** The maximum number of iterations to perform. */
  public int ITERATION_CUTOFF = Integer.MAX_VALUE;

  private final boolean handleCallApply;

  private FlowGraphBuilder builder;

  private final int bound;

  private IRFactory<IMethod> factoryir = AstIRFactory.makeDefaultFactory();

  private Map<IMethod, Boolean> funcsUsingArgumentsArray = new HashMap<>();
  private Map<IMethod, Boolean> funcsUsingLessParsThanDefined = new HashMap<>();
  List<CAstBinaryOp> binaryOpList =
      new ArrayList<>(
          Arrays.asList(
              CAstBinaryOp.EQ, CAstBinaryOp.NE, CAstBinaryOp.STRICT_EQ, CAstBinaryOp.STRICT_NE));

  public WorklistBasedOptimisticCallgraphBuilder(
      IClassHierarchy cha,
      AnalysisOptions options,
      IAnalysisCacheView cache,
      boolean supportFullPointerAnalysis,
      int bound) {
    super(cha, options, cache, supportFullPointerAnalysis);
    handleCallApply =
        options instanceof JSAnalysisOptions && ((JSAnalysisOptions) options).handleCallApply();
    this.bound = bound;
  }

  @Override
  public FlowGraph buildFlowGraph(IProgressMonitor monitor) throws CancelException {
    builder = new FlowGraphBuilder(cha, cache, false);
    return builder.buildFlowGraph();
  }

  private MutableIntSet findOrCreateMutableIntSet(Map<Vertex, MutableIntSet> M, Vertex v) {
    if (M == null) {
      throw new IllegalArgumentException("M is null");
    }
    MutableIntSet mis = M.get(v);
    if (mis == null) {
      mis = new MutableSharedBitVectorIntSet();
      M.put(v, mis);
    }
    return mis;
  }

  @Override
  public Set<Pair<CallVertex, FuncVertex>> extractCallGraphEdges(
      FlowGraph flowgraph, IProgressMonitor monitor) throws CancelException {
    VertexFactory factory = flowgraph.getVertexFactory();
    Set<Vertex> worklist = HashSetFactory.make();
    // Map<Vertex, Set<FuncVertex>> reachingFunctions = HashMapFactory.make();
    OrdinalSetMapping<FuncVertex> mapping = new MutableMapping<>(new FuncVertex[100]);
    Map<Vertex, MutableIntSet> reachingFunctions = HashMapFactory.make();
    Map<VarVertex, Pair<JavaScriptInvoke, Boolean>> reflectiveCalleeVertices =
        HashMapFactory.make();
    /** maps to maintain the list of reachable calls that are yet to be processed * */
    Map<Vertex, Set<FuncVertex>> pendingCallWorklist = HashMapFactory.make();
    Map<Vertex, Set<FuncVertex>> pendingReflectiveCallWorklist = HashMapFactory.make();
    Set<Vertex> pendingFlowWorklist = HashSetFactory.make();

    for (Vertex v : flowgraph) {
      if (v instanceof FuncVertex) {
        FuncVertex fv = (FuncVertex) v;
        worklist.add(fv);
        int mappedVal = mapping.add(fv);
        findOrCreateMutableIntSet(reachingFunctions, fv).add(mappedVal);
        // MapUtil.findOrCreateSet(reachingFunctions, fv).add(fv);
      }
    }
    int cnt = 0;
    int flowCnt = 0;
    int flowBound = 20;
    /**
     * if bound is missing, calledges are added until all worklists are empty else, the calledges
     * are added until the bound value is hit *
     */
    while ((bound == -1
            && (!worklist.isEmpty()
                || !pendingCallWorklist.isEmpty()
                || !pendingReflectiveCallWorklist.isEmpty()))
        || (cnt < bound
            && (!worklist.isEmpty()
                || !pendingFlowWorklist.isEmpty()
                || !pendingCallWorklist.isEmpty()
                || !pendingReflectiveCallWorklist.isEmpty()))) {
      if (pendingFlowWorklist.isEmpty()) {
        processPendingCallWorklist(
            flowgraph,
            pendingCallWorklist,
            factory,
            reachingFunctions,
            reflectiveCalleeVertices,
                pendingFlowWorklist,
            mapping);
        processPendingReflectiveCallWorklist(
            flowgraph, pendingReflectiveCallWorklist, reflectiveCalleeVertices, pendingFlowWorklist);
        pendingCallWorklist.clear();
        pendingReflectiveCallWorklist.clear();
      }
      while (flowCnt < flowBound &&
              ( !pendingFlowWorklist.isEmpty()
                || !worklist.isEmpty())) {
        if(worklist.isEmpty()){
          worklist.addAll(pendingFlowWorklist);
          pendingFlowWorklist.clear();
          flowCnt +=1;
        }
        MonitorUtil.throwExceptionIfCanceled(monitor);

        Vertex v = worklist.iterator().next();
        worklist.remove(v);
        // Set<FuncVertex> vReach = MapUtil.findOrCreateSet(reachingFunctions, v);
        MutableIntSet vReach = findOrCreateMutableIntSet(reachingFunctions, v);
        for (Vertex w : Iterator2Iterable.make(flowgraph.getSucc(v))) {
          MonitorUtil.throwExceptionIfCanceled(monitor);

          // Set<FuncVertex> wReach = MapUtil.findOrCreateSet(reachingFunctions, w);
          MutableIntSet wReach = findOrCreateMutableIntSet(reachingFunctions, w);
          boolean changed = false;
          if (w instanceof CallVertex) {
            // for (FuncVertex fv : vReach) {
            // if (wReach.add(fv)) {
            IntIterator mappedFuncs = vReach.intIterator();
            while (mappedFuncs.hasNext()) {
              FuncVertex fv = mapping.getMappedObject(mappedFuncs.next());
              IMethod im = fv.getConcreteType().getMethod(AstMethodReference.fnSelector);
              if ((((CallVertex) w).toSourceLevelString(cache).contains("preamble.js")
                      || ((CallVertex) w).toSourceLevelString(cache).contains("prologue.js"))
                  && !(fv.getFullName().equals("Lprologue.js/Function_prototype_call")
                      || fv.getFullName().equals("Lprologue.js/Function_prototype_apply"))) {
                continue;
              }

              if (im == null) {
                if (wReach.add(mapping.getMappedIndex(fv))) {
                  changed = true;
                  MapUtil.findOrCreateSet(pendingCallWorklist, w).add(fv);
                }
              } else if (im != null) {
                int noOfPassedParameters =
                    ((CallVertex) w).getInstruction().getNumberOfPositionalParameters();
                int noOfDefinedParameters = im.getNumberOfParameters();
                if (!((CallVertex) w).isNew() && noOfPassedParameters == noOfDefinedParameters) {
                  if (wReach.add(mapping.getMappedIndex(fv))) {
                    changed = true;
                    MapUtil.findOrCreateSet(pendingCallWorklist, w).add(fv);
                  }
                } else if ((((CallVertex) w).isNew()
                        && noOfPassedParameters < noOfDefinedParameters)
                    || (!((CallVertex) w).isNew()
                        && noOfPassedParameters < noOfDefinedParameters)) {
                  if (fv.toSourceLevelString(cache).contains("preamble.js") || fv.toSourceLevelString(cache).contains("prologue.js") || useOfArgumentsArray(im)) {
                    if (wReach.add(mapping.getMappedIndex(fv))) {
                      changed = true;
                      MapUtil.findOrCreateSet(pendingCallWorklist, w).add(fv);
                    }
                  } else {
                    if (usingLessParsThanDefined(
                        ((CallVertex) w).getInstruction(), im, false, ((CallVertex) w).isNew())) {
                      if (wReach.add(mapping.getMappedIndex(fv))) {
                        changed = true;
                        MapUtil.findOrCreateSet(pendingCallWorklist, w).add(fv);
                      }
                    }
                  }
                } else if ((((CallVertex) w).isNew()
                        && noOfPassedParameters >= noOfDefinedParameters)
                    || (!((CallVertex) w).isNew()
                        && noOfPassedParameters > noOfDefinedParameters)) {
                  if ( (((CallVertex) w).isNew() && noOfPassedParameters + 1 == noOfDefinedParameters)
                      || useOfArgumentsArray(im)) {
                    if (wReach.add(mapping.getMappedIndex(fv))) {
                      changed = true;
                      MapUtil.findOrCreateSet(pendingCallWorklist, w).add(fv);
                    }
                  }
                }
              }
            }
          } else if (handleCallApply && reflectiveCalleeVertices.containsKey(w)) {
            // for (FuncVertex fv : vReach) {
            // if (wReach.add(fv)) {
            IntIterator mappedFuncs = vReach.intIterator();
            while (mappedFuncs.hasNext()) {
              FuncVertex fv = mapping.getMappedObject(mappedFuncs.next());
              if (wReach.add(mapping.getMappedIndex(fv))) {
                changed = true;
                MapUtil.findOrCreateSet(pendingReflectiveCallWorklist, (VarVertex) w).add(fv);
              }
            }
          } else {

            changed = wReach.addAll(vReach);
          }
          //if (changed) worklist.add(w);
          if (changed) {
            pendingFlowWorklist.add(w);
          }
        }
      }
      cnt += 1;
    }

    System.out.println("The last executed bound was : " + cnt);
    System.out.println("The last executed flow bound was : " + flowCnt);

    Set<Pair<CallVertex, FuncVertex>> res = HashSetFactory.make();
    // for (Map.Entry<Vertex, Set<FuncVertex>> entry : reachingFunctions.entrySet()) {
    for (Map.Entry<Vertex, MutableIntSet> entry : reachingFunctions.entrySet()) {
      final Vertex v = entry.getKey();
      // if (v instanceof CallVertex)
      // for (FuncVertex fv : entry.getValue()) res.add(Pair.make((CallVertex) v, fv));
      if (v instanceof CallVertex) {
        IntIterator mapped = entry.getValue().intIterator();
        while (mapped.hasNext()) {
          FuncVertex fv = mapping.getMappedObject(mapped.next());
          res.add(Pair.make((CallVertex) v, fv));
        }
      }
    }
    return res;
  }

  public void processPendingCallWorklist(
      FlowGraph flowgraph,
      Map<Vertex, Set<FuncVertex>> pendingCallWorklist,
      VertexFactory factory,
      Map<Vertex, MutableIntSet> reachingFunctions,
      Map<VarVertex, Pair<JavaScriptInvoke, Boolean>> reflectiveCalleeVertices,
      Set<Vertex> worklist,
      OrdinalSetMapping<FuncVertex> mapping) {
    for (Map.Entry<Vertex, Set<FuncVertex>> entry : pendingCallWorklist.entrySet()) {
      CallVertex callVertex = (CallVertex) entry.getKey();
      for (FuncVertex fv : entry.getValue()) {
        addCallEdge(flowgraph, callVertex, fv, worklist);
        String fullName = fv.getFullName();
        if (handleCallApply
            && (fullName.equals("Lprologue.js/Function_prototype_call")
                || fullName.equals("Lprologue.js/Function_prototype_apply"))) {
          JavaScriptInvoke invk = callVertex.getInstruction();
          VarVertex reflectiveCalleeVertex =
              factory.makeVarVertex(callVertex.getCaller(), invk.getUse(1));
          // IMethod im = fv.getConcreteType().getMethod(AstMethodReference.fnSelector);
          // if(invk.getNumberOfPositionalParameters() == im.getNumberOfParameters()){
          flowgraph.addEdge(
              reflectiveCalleeVertex,
              factory.makeReflectiveCallVertex(callVertex.getCaller(), invk));
          // }
          // we only add dataflow edges for Function.prototype.call
          boolean isCall = fullName.equals("Lprologue.js/Function_prototype_call");
          reflectiveCalleeVertices.put(reflectiveCalleeVertex, Pair.make(invk, isCall));
          // for (FuncVertex fw : MapUtil.findOrCreateSet(reachingFunctions,
          // reflectiveCalleeVertex))
          // addReflectiveCallEdge(flowgraph, reflectiveCalleeVertex, invk, fw, worklist, isCall);
          IntIterator reflectiveCalleeMapped =
              findOrCreateMutableIntSet(reachingFunctions, reflectiveCalleeVertex).intIterator();
          while (reflectiveCalleeMapped.hasNext()) {
            FuncVertex fw = mapping.getMappedObject(reflectiveCalleeMapped.next());
            IMethod im2 = fw.getConcreteType().getMethod(AstMethodReference.fnSelector);
            if(isCall){
              if(!(callVertex.toSourceLevelString(cache).contains("preamble.js")
                      || callVertex.toSourceLevelString(cache).contains("prologue.js")) && im2!=null){
              if (invk.getNumberOfPositionalParameters() < im2.getNumberOfParameters()
                  && useOfArgumentsArray(im2)) {
                addReflectiveCallEdge(flowgraph, reflectiveCalleeVertex, invk, fw, worklist, isCall);
              } else if (invk.getNumberOfPositionalParameters() >= im2.getNumberOfParameters()) {
                if (useOfArgumentsArray(im2) || usingLessParsThanDefined(invk,im2,true,false)) {
                  addReflectiveCallEdge(
                      flowgraph, reflectiveCalleeVertex, invk, fw, worklist, isCall);
                }
              }
              }
            }else{
              addReflectiveCallEdge(
                      flowgraph, reflectiveCalleeVertex, invk, fw, worklist, isCall);
            }
          }
        }
      }
    }
  }

  public void processPendingReflectiveCallWorklist(
      FlowGraph flowgraph,
      Map<Vertex, Set<FuncVertex>> pendingReflectiveCallWorklist,
      Map<VarVertex, Pair<JavaScriptInvoke, Boolean>> reflectiveCalleeVertices,
      Set<Vertex> worklist) {
    for (Map.Entry<Vertex, Set<FuncVertex>> entry : pendingReflectiveCallWorklist.entrySet()) {
      final Vertex v = entry.getKey();
      Pair<JavaScriptInvoke, Boolean> invkAndIsCall = reflectiveCalleeVertices.get(v);
      for (FuncVertex fv : entry.getValue()) {
        IMethod im = fv.getConcreteType().getMethod(AstMethodReference.fnSelector);
        if(invkAndIsCall.snd){
          if (invkAndIsCall.fst.getNumberOfPositionalParameters() >= im.getNumberOfParameters()){
             if (invkAndIsCall.fst.getNumberOfPositionalParameters()
                     == im.getNumberOfParameters() + 1 || useOfArgumentsArray(im)) {
              addReflectiveCallEdge(
                  flowgraph, (VarVertex) v, invkAndIsCall.fst, fv, worklist, invkAndIsCall.snd);
              }
          } else if (invkAndIsCall.fst.getNumberOfPositionalParameters() < im.getNumberOfParameters()) {
            if (useOfArgumentsArray(im)
                || usingLessParsThanDefined(invkAndIsCall.fst, im, invkAndIsCall.snd, false)) {
              addReflectiveCallEdge(
                  flowgraph, (VarVertex) v, invkAndIsCall.fst, fv, worklist, invkAndIsCall.snd);
            }
          }
        }else{
          addReflectiveCallEdge(
                  flowgraph, (VarVertex) v, invkAndIsCall.fst, fv, worklist, invkAndIsCall.snd);
        }
      }
    }
  }
  // add flow corresponding to a new call edge
  private void addCallEdge(
      FlowGraph flowgraph, CallVertex c, FuncVertex callee, Set<Vertex> worklist) {
    VertexFactory factory = flowgraph.getVertexFactory();
    FuncVertex caller = c.getCaller();
    JavaScriptInvoke invk = c.getInstruction();

    int offset = 0;
    if (invk.getDeclaredTarget()
        .getSelector()
        .equals(JavaScriptMethods.ctorReference.getSelector())) {
      offset = 1;
    }

    for (int i = 0; i < invk.getNumberOfPositionalParameters(); ++i) {
      // only flow receiver into 'this' if invk is, in fact, a method call
      flowgraph.addEdge(
          factory.makeVarVertex(caller, invk.getUse(i)), factory.makeArgVertex(callee));
      if (i != 1 || !invk.getDeclaredTarget().getSelector().equals(AstMethodReference.fnSelector))
        addFlowEdge(
            flowgraph,
            factory.makeVarVertex(caller, invk.getUse(i)),
            factory.makeParamVertex(callee, i + offset),
            worklist);
    }

    // flow from return vertex to result vertex
    addFlowEdge(
        flowgraph,
        factory.makeRetVertex(callee),
        factory.makeVarVertex(caller, invk.getDef()),
        worklist);
  }

  public void addFlowEdge(FlowGraph flowgraph, Vertex from, Vertex to, Set<Vertex> worklist) {
    flowgraph.addEdge(from, to);
    worklist.add(from);
  }

  // add data flow corresponding to a reflective invocation via Function.prototype.call
  // NB: for f.call(...), f will _not_ appear as a call target, but the appropriate argument and
  // return data flow will be set up
  private void addReflectiveCallEdge(
      FlowGraph flowgraph,
      VarVertex reflectiveCallee,
      JavaScriptInvoke invk,
      FuncVertex realCallee,
      Set<Vertex> worklist,
      boolean isFunctionPrototypeCall) {
    VertexFactory factory = flowgraph.getVertexFactory();
    FuncVertex caller = reflectiveCallee.getFunction();
    // IMethod im = realCallee.getConcreteType().getMethod(AstMethodReference.fnSelector);
    // if(invk.getNumberOfPositionalParameters() == im.getNumberOfParameters()){
    if (isFunctionPrototypeCall) {
      // flow from arguments to parameters
      for (int i = 2; i < invk.getNumberOfPositionalParameters(); ++i) {
        addFlowEdge(
            flowgraph,
            factory.makeVarVertex(caller, invk.getUse(i)),
            factory.makeParamVertex(realCallee, i - 1),
            worklist);
      }
    }

    // flow from return vertex to result vertex
    addFlowEdge(
        flowgraph,
        factory.makeRetVertex(realCallee),
        factory.makeVarVertex(caller, invk.getDef()),
        worklist);
  }
  // }

  private boolean useOfArgumentsArray(IMethod im) {
    if (funcsUsingArgumentsArray.containsKey(im)) {
      return funcsUsingArgumentsArray.get(im);
    } else {
      IR ir = factoryir.makeIR(im, Everywhere.EVERYWHERE, new SSAOptions());
      DefUse du = new DefUse(ir);
      SSAInstruction[] statements = ir.getInstructions();
      int instNum = statements[0].getDef();
      boolean argumentsArrUse = false;
      try {
        Iterator<SSAInstruction> instNumUse = du.getUses(instNum);
        if (instNumUse.hasNext()) {
          argumentsArrUse = true;
        }
      } catch (ArrayIndexOutOfBoundsException exception) {
        argumentsArrUse = true;
      }
      funcsUsingArgumentsArray.put(im, argumentsArrUse);
      return argumentsArrUse;
    }
  }

  private boolean usingLessParsThanDefined(
      JavaScriptInvoke invk, IMethod im, boolean isCallorApply, boolean isNew) {
    boolean allUsed = true;
    if (funcsUsingLessParsThanDefined.containsKey(im)) {
      allUsed = funcsUsingLessParsThanDefined.get(im);
    } else {
      IR ir = factoryir.makeIR(im, Everywhere.EVERYWHERE, new SSAOptions());

      Map<Integer, Boolean> extraParsList = new HashMap<>();
      int i = 0;
      if (isNew) {
        i = invk.getNumberOfPositionalParameters() + 2;
      } else if (isCallorApply) {
        i = invk.getNumberOfPositionalParameters();
      } else {
        i = invk.getNumberOfPositionalParameters() + 1;
      }
      for (; i <= im.getNumberOfParameters(); i++) {
        extraParsList.put(i, false);
      }
      for (SSAInstruction statement : ir.getInstructions()) {
        if (statement instanceof SSAConditionalBranchInstruction
            || (statement instanceof SSAUnaryOpInstruction
                && ((SSAUnaryOpInstruction) statement).getOpcode()
                    == IUnaryOpInstruction.Operator.NEG)
            || (statement instanceof SSABinaryOpInstruction
                && binaryOpList.contains(((SSABinaryOpInstruction) statement).getOperator()))
            || statement instanceof SSAAbstractInvokeInstruction) {
          for (int j = 0; j < statement.getNumberOfUses(); j++) {
            if (extraParsList.containsKey(statement.getUse(j))) {
              extraParsList.put(statement.getUse(j), true);
            }
          }
        }
      }

      for (SSAInstruction inst : Iterator2Iterable.make(ir.iteratePhis())){
        //if (inst instanceof SSAPhiInstruction){
        SSAPhiInstruction phi = (SSAPhiInstruction) inst;
        if (phi == null) {
          continue;
        }else{
          for (int j = 0; j < inst.getNumberOfUses(); j++) {
            if (extraParsList.containsKey(inst.getUse(j))) {
              extraParsList.put(inst.getUse(j), true);
            }
          }
        }
      }

      for (Boolean value : extraParsList.values()) {
        if (!value) {
          allUsed = false;
          break;
        }
      }
    }
    if (allUsed) {
      funcsUsingLessParsThanDefined.put(im, true);
      return true;
    } else {
      funcsUsingLessParsThanDefined.put(im, false);
      return false;
    }
  }
}
