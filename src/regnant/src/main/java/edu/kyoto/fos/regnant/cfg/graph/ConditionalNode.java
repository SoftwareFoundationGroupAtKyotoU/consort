package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

public class ConditionalNode extends GraphElem {
  public final Continuation tBranch, fBranch;
  public final BasicBlock head;
  private final Jumps jumps;

  public ConditionalNode(final BasicBlock curr, final Jumps hdJumps, final Continuation trCont, final Continuation flCont) {
    this.head = curr;
    this.jumps = hdJumps;
    this.tBranch = trCont;
    this.fBranch = flCont;
  }

  @Override public Jumps getJumps() {
    return jumps;
  }

  @Override public BasicBlock getHead() {
    return head;
  }

  @Override public void printAt(final int i, final StringBuilder sb) {
    indentAndLoop(i, sb).append(head.getId()).append(" : ite {\n");
    tBranch.printAt(i + 1, sb); sb.append("\n");
    indent(i, sb).append("} else {\n");
    fBranch.printAt(i + 1, sb); sb.append("\n");
    indent(i, sb).append("}");
  }
}
