package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.List;
import java.util.stream.Collectors;

public class InstNode extends GraphElem {
  public final List<GraphElem> hds;

  public InstNode(final List<GraphElem> hds) {
    this.hds = hds;
    assert hds.stream().noneMatch(p -> p instanceof InstNode);
  }

  @Override public Jumps getJumps() {
    return hds.stream().map(GraphElem::getJumps).reduce(Jumps::union).get();
  }

  @Override public BasicBlock getHead() {
    return null;
  }

  @Override public List<BasicBlock> heads() {
    return hds.stream().map(GraphElem::getHead).collect(Collectors.toList());
  }

  @Override public void printAt(final int i, final StringBuilder sb) {
    indent(i, sb).append("choice {\n");
    hds.forEach(ge -> { ge.printAt(i + 1, sb); sb.append('\n'); });
    indent(i, sb).append("}\n");
  }
}
