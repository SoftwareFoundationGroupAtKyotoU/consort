package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.Optional;

public class JumpNode extends GraphElem implements TerminalNode {
  public BasicBlock head;
  private final Jumps j;

  public JumpNode(final BasicBlock curr, final Jumps nodeJump) {
    super();
    this.head = curr;
    this.j = nodeJump;
  }

  @Override public Jumps getJumps() {
    return j;
  }

  @Override public BasicBlock getHead() {
    return head;
  }

  @Override public void printAt(final int i, final StringBuilder sb) {
    indentAndLoop(i, sb).append(this.head.getId()).append(" -> ").append(j.toString());
  }

  @Override public Optional<Coord> getCoord() {
    return Optional.of(new Coord(this.head));
  }
}
