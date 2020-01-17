package edu.kyoto.fos.regnant.cfg;

import java.util.List;
import java.util.Optional;

public class AnnotatedEdge {
  public final List<Loop> brk;
  public final Optional<Loop> cont;
  public final BasicBlock block;

  public AnnotatedEdge(List<Loop> brk, Optional<Loop> cont, BasicBlock block) {
    this.brk = brk;
    this.cont = cont;
    this.block = block;
  }

}
