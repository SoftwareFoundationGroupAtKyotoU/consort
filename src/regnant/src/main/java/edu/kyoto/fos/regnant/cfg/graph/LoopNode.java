package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

public class LoopNode extends GraphElem {
  private final Jumps jumps;
  public final GraphElem loopBody;

  @Override public boolean isLoop() {
    return true;
  }

  public LoopNode(GraphElem elem, Jumps j) {
    this.loopBody = elem;
    assert !(loopBody instanceof BlockSequence) : elem;
    this.jumps = j;
  }

  @Override public BasicBlock getHead() {
    return this.loopBody.getHead();
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("loop (").append(this.loopBody.getHead().getId()).append(") {\n");
    this.loopBody.printAt(level + 1, b);
    b.append("\n");
    indent(level, b).append("}\n");
  }

  @Override public Jumps getJumps() {
    return this.jumps;
  }
}
