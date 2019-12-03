package edu.kyoto.fos.regnant.cfg;

import java.util.ArrayList;
import java.util.List;

public class AnnotatedBasicBlockGraph {
  private final BasicBlockGraph bbg;
  private final LoopTree lt;

  public AnnotatedBasicBlockGraph(BasicBlockGraph bbg, LoopTree lt) {
    this.bbg = bbg;
    this.lt = lt;
  }

  public List<AnnotatedEdge> getSucc(BasicBlock b) {
    List<Loop> currLoops = this.lt.containingLoops(b);
    List<AnnotatedEdge> toReturn = new ArrayList<>();
    for(BasicBlock succ : bbg.getSuccsOf(b)) {
      List<Loop> succLoops = this.lt.containingLoops(succ);
      final List<Loop> cont = new ArrayList<>();
      final List<Loop> brk = new ArrayList<>();
      succLoops.forEach(sl ->{
        if(currLoops.contains(sl) && sl.getHeader().equals(succ)) {
          cont.add(sl);
        }
      });
      currLoops.stream().filter(l -> !succLoops.contains(l)).forEach(brk::add);
      assert (cont.size() <= 1);
      toReturn.add(new AnnotatedEdge(brk, cont.stream().findFirst(), succ));
    }
    return toReturn;
  }

  public BasicBlock getHead() {
    return bbg.getHeads().get(0);
  }

  public BasicBlockGraph getRawGraph() {
    return bbg;
  }
}
