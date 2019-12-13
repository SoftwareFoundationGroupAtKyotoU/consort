package edu.kyoto.fos.regnant.cfg;

import edu.kyoto.fos.regnant.cfg.graph.BlockSequence;
import edu.kyoto.fos.regnant.cfg.graph.ConditionalNode;
import edu.kyoto.fos.regnant.cfg.graph.Continuation;
import edu.kyoto.fos.regnant.cfg.graph.Coord;
import edu.kyoto.fos.regnant.cfg.graph.ElemCont;
import edu.kyoto.fos.regnant.cfg.graph.GraphElem;
import edu.kyoto.fos.regnant.cfg.graph.InstNode;
import edu.kyoto.fos.regnant.cfg.graph.JumpCont;
import edu.kyoto.fos.regnant.cfg.graph.JumpNode;
import edu.kyoto.fos.regnant.cfg.graph.Jumps;
import edu.kyoto.fos.regnant.cfg.graph.LoopNode;
import fj.P;
import fj.P2;
import soot.Body;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.jimple.IfStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DominatorTree;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.HashMutableDirectedGraph;
import soot.toolkits.graph.MHGDominatorsFinder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.Stream.Builder;

public class CFGReconstructor {
  private final BasicBlockMapper bbm;
  private final LoopTree lt;
  private final UnitPatchingChain unitChain;
  private final AnnotatedBasicBlockGraph graph;
  private GraphElem cfgRoot;
  private BlockTree<BasicBlock> bt;
  private Set<Coord> recurseJumps = new TreeSet<>();

  public CFGReconstructor(Body b) {
    this.bbm = new BasicBlockMapper(b);
    this.unitChain = b.getUnits();
    BasicBlockGraph bbg = new BasicBlockGraph(new BriefUnitGraph(b), bbm);
    this.lt = new LoopFinder(bbg).getTree();
    this.graph = new AnnotatedBasicBlockGraph(bbg,lt);
    computeCFG();
  }

  private void computeCFG() {
    DominatorsFinder<BasicBlock> doms = new MHGDominatorsFinder<>(graph.getRawGraph());
    DominatorTree<BasicBlock> dt = new DominatorTree<>(doms);
    assert dt.getHead().getGode().equals(graph.getHead());

    this.cfgRoot = recursiveLayout(dt);
  }

  public GraphElem getReconstructedGraph() {
    return cfgRoot;
  }

  public BlockTree<BasicBlock> getStructure() {
    return this.bt;
  }

  public String dump() {
    this.bbm.iterator().forEachRemaining(System.out::println);
    return this.cfgRoot.dump();
  }

  private GraphElem recursiveLayout(DominatorTree<BasicBlock> dt) {
    this.bt = new BlockTree<>(dt);
    recursiveLift(dt.getHead().getGode(), null, null);
    return recursiveLayout(bt, graph.getHead(), null);
  }

  private void recursiveLift(final BasicBlock node, final BasicBlock head, final Builder<BasicBlock> outQueue) {
    if(head != null) {
      if(this.lt.containingLoops(node).stream().map(Loop::getHeader).noneMatch(head::equals)) {
        outQueue.accept(node);
        return;
      }
    }
    List<BasicBlock> children = new ArrayList<>(this.bt.children.getOrDefault(node, Collections.emptyList()));
    if(lt.isLoopHeader(node)) {
      Stream.Builder<BasicBlock> b = Stream.builder();
      children.forEach(n -> {
        recursiveLift(n, node, b);
      });
      b.build().forEach(n -> {
        if((this.lt.containingLoops(n).isEmpty() && head == null) ||
            this.lt.containingLoops(n).stream().map(Loop::getHeader).anyMatch(p -> p.equals(head))) {
          this.bt.shiftTo(n, this.bt.parent.get(node));
        } else {
          assert outQueue != null : n + " " + node;
          outQueue.accept(n);
        }
      });
    } else {
      children.forEach(b -> recursiveLift(b, head, outQueue));
    }
  }

  private Unit fwMap(Unit u) {
    if(u.hasTag(RemapTag.REMAP)) {
      return ((RemapTag)u.getTag(RemapTag.REMAP)).target;
    } else {
      return u;
    }
  }


  private P2<AnnotatedEdge, AnnotatedEdge> getConditionalEdges(BasicBlock b) {
    IfStmt s = (IfStmt) b.getTail();
    BasicBlock ft = this.bbm.getBlockByHead(fwMap(this.unitChain.getSuccOf(s)));
    BasicBlock tgt = this.bbm.getBlockByHead(fwMap(s.getTarget()));
    List<AnnotatedEdge> succ = this.graph.getSucc(b);
    AnnotatedEdge tgtEdge = succ.stream().filter(e -> e.block.equals(tgt)).findAny().get();
    AnnotatedEdge ftEdge = succ.stream().filter(e -> e.block.equals(ft)).findAny().get();
    return P.p(tgtEdge, ftEdge);
  }

  private GraphElem recursiveLayout(final BlockTree<BasicBlock> bt, final BasicBlock curr, BasicBlock loopHeader) {
    List<BasicBlock> childBlocks = bt.children.get(curr);
    // a return then
    List<AnnotatedEdge> succ = this.graph.getSucc(curr);
    if(succ.size() == 0) {
      return new JumpNode(curr, Jumps.ret(curr));
    }

    boolean isLoopHeader = lt.isLoopHeader(curr);
    BasicBlock childHeaders = isLoopHeader ? curr : loopHeader;
    List<GraphElem> gElem = childBlocks.stream().map(cb -> recursiveLayout(bt, cb, childHeaders)).collect(Collectors.toList());
    Map<BasicBlock, GraphElem> lkp = gElem.stream().collect(Collectors.toMap(GraphElem::getHead, i -> i));
    HashMutableDirectedGraph<BasicBlock> depGraph = new HashMutableDirectedGraph<>();
    lkp.keySet().forEach(depGraph::addNode);
    lkp.forEach((bb, elem) -> elem.getJumps().flow.stream().map(P2::_2).filter(lkp::containsKey).forEach(tgt -> depGraph.addEdge(bb, tgt)));

    // these are the flow describing the exits from this entire subtree
    Jumps exitFlows = new Jumps();
    ArrayList<GraphElem> elems = new ArrayList<>();
    if(succ.size() == 2) {
      P2<AnnotatedEdge, AnnotatedEdge> v = this.getConditionalEdges(curr);
      Jumps hdJumps = new Jumps();

      Continuation trCont = this.toContinuation(Coord.of(true, curr), depGraph, v._1(), lkp);
      Continuation flCont = this.toContinuation(Coord.of(false, curr), depGraph, v._2(), lkp);
      // Now compute the jumps for the hd element
      mergeParentJumps(curr, hdJumps, exitFlows, lkp, trCont.getJumps(), loopHeader);
      mergeParentJumps(curr, hdJumps, exitFlows, lkp, flCont.getJumps(), loopHeader);
      elems.add(new ConditionalNode(curr, hdJumps, trCont, flCont));
    } else {
      assert succ.size() == 1;
      Coord c = Coord.of(curr);
      AnnotatedEdge e = this.graph.getSucc(curr).get(0);
      this.saveRecurse(c, e);
      Jumps j = Jumps.of(c, e);
      Jumps nodeJump = new Jumps();
      mergeParentJumps(curr, nodeJump, exitFlows, lkp, j, loopHeader);
      elems.add(new JumpNode(curr, nodeJump));
    }
    while(depGraph.size() > 0) {
      List<BasicBlock> next = depGraph.getHeads();
      assert next.size() > 0;
      assert next.stream().allMatch(lkp::containsKey);
      next.stream().map(lkp::get).map(GraphElem::getJumps).forEach(j -> mergeSuccessorJumps(curr, exitFlows, lkp, j, loopHeader));
      if(next.size() == 1) {
        elems.add(lkp.get(next.get(0)));
      } else {
        InstNode n = new InstNode(next.stream().map(lkp::get).collect(Collectors.toList()));
        elems.add(n);
      }
      next.forEach(depGraph::removeNode);
    }

    if(elems.size() > 1) {
      return new BlockSequence(elems, exitFlows, isLoopHeader);
    } else {
      GraphElem toRet = elems.get(0);
      if(isLoopHeader) {
        return new LoopNode(toRet, exitFlows);
      } else {
        return toRet;
      }
    }
  }

  private void saveRecurse(final Coord c, final AnnotatedEdge e) {
    if(e.cont.isPresent() && e.brk.isEmpty()) {
      this.recurseJumps.add(c);
    }
  }

  private void mergeSuccessorJumps(BasicBlock curr, final Jumps exitFlows, Map<BasicBlock, GraphElem> lkp, Jumps j, BasicBlock loopHeader) {
    mergeJump(curr, exitFlows, j, flow -> !lkp.containsKey(flow._2()), true, loopHeader);
  }

  private void mergeParentJumps(BasicBlock curr, final Jumps hdJumps, final Jumps exitFlows, final Map<BasicBlock, GraphElem> lkp, final Jumps cont, final BasicBlock loopHeader) {
    mergeJump(curr, hdJumps, cont, tgt -> true, false, loopHeader);
    mergeJump(curr, exitFlows, cont, tgt -> !lkp.containsKey(tgt._2()), true, loopHeader);
  }

  private void mergeJump(BasicBlock curr, Jumps tgtJumps, Jumps srcJumps, Predicate<P2<Coord, BasicBlock>> isFlow, boolean breakAsFlow, final BasicBlock loopHeader) {
    srcJumps.flow.forEach(f -> {
      if(isFlow.test(f)) {
        tgtJumps.flow.add(f);
      }
    });
    srcJumps.brk.forEach((coord, headers) -> {
      // this may be a break, check if we propagate the break, or turn it into a flow
      Set<BasicBlock> newHead;
      if(headers.contains(curr)) {
        newHead = headers.stream().filter(p -> !curr.equals(p)).collect(Collectors.toSet());
        // this is the outer most break location, transform this break into a flow
        if(newHead.isEmpty()) {
          if(breakAsFlow) {
            if(coord._2().equals(loopHeader)) {
              tgtJumps.cont.add(coord);
            } else {
              tgtJumps.flow.add(coord);
            }
            return;
          } else {
            newHead = new HashSet<>(headers);
          }
        }
      } else {
        newHead = new HashSet<>(headers);
      }
      assert !newHead.isEmpty();
      tgtJumps.brk.computeIfAbsent(coord, ign -> new HashSet<>()).addAll(newHead);
    });
  }

  private Continuation toContinuation(final Coord coord, final HashMutableDirectedGraph<BasicBlock> depGraph,
      final AnnotatedEdge annotatedEdge, Map<BasicBlock, GraphElem> lkp) {
    if(!depGraph.containsNode(annotatedEdge.block) || !depGraph.getHeads().contains(annotatedEdge.block)) {
      this.saveRecurse(coord, annotatedEdge);
      return JumpCont.of(coord, annotatedEdge);
    } else {
      assert lkp.containsKey(annotatedEdge.block);
      depGraph.removeNode(annotatedEdge.block);
      return new ElemCont(lkp.get(annotatedEdge.block));
    }
  }

  public Collection<? extends Coord> getRecurseLocations() {
    return recurseJumps;
  }
}
