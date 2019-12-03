package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.List;
import java.util.stream.Collectors;

public class BlockSequence extends GraphElem {
  public List<GraphElem> chain;
  public Jumps jumps;

  public BlockSequence(final List<GraphElem> elems, final Jumps j, boolean isLoop) {
    super(isLoop);
    assert elems.size() > 1 : elems.stream().map(GraphElem::dump).collect(Collectors.toList());
    this.chain = elems;
    this.jumps = j;
  }

  @Override public Jumps getJumps() {
    return jumps;
  }

  @Override public BasicBlock getHead() {
    return chain.get(0).getHead();
  }

  @Override public void printAt(final int i, StringBuilder sb) {
    indentAndLoop(i, sb).append("{\n");
    chain.forEach(ge -> { ge.printAt(i + 1, sb); sb.append("\n"); });
    indent(i, sb).append("}\n");
  }
}
