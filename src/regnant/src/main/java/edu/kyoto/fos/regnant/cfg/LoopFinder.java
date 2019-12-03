package edu.kyoto.fos.regnant.cfg;

import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.MHGDominatorsFinder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

public class LoopFinder {
  private final LoopTree tree;
  private BasicBlockGraph bbg;

  public LoopFinder(BasicBlockGraph bbg) {
    this.bbg = bbg;
    this.tree = computeLoopTree();
  }

  private LoopTree computeLoopTree() {
    DominatorsFinder<BasicBlock> df = new MHGDominatorsFinder<>(this.bbg);

    Map<BasicBlock, Set<BasicBlock>> loopMap = new HashMap<>();
    for(BasicBlock bb : this.bbg) {
      Set<BasicBlock> headers = new HashSet<>();
      for(BasicBlock s : this.bbg.getSuccsOf(bb)) {
        if(df.isDominatedBy(bb, s)) {
          headers.add(s);
        }
      }
      for(BasicBlock header : headers) {
        Set<BasicBlock> body = bodyFor(header, bb);
        loopMap.merge(header, body, (s1, s2) -> {
          s1.addAll(s2); return s1;
        });
      }
    }
    return new LoopTree(loopMap);
  }

  public LoopTree getTree() {
    return tree;
  }

  private Set<BasicBlock> bodyFor(final BasicBlock header, final BasicBlock bb) {
    LinkedList<BasicBlock> wl = new LinkedList<>();
    wl.add(bb);
    Set<BasicBlock> toRet = new HashSet<>();
    while(!wl.isEmpty()) {
      BasicBlock b = wl.pop();
      if(b.equals(header)) {
        continue;
      }
      if(!toRet.add(b) ) {
        continue;
      }
      wl.addAll(this.bbg.getPredsOf(b));
    }
    return toRet;
  }
}
