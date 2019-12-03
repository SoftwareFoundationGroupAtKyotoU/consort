package edu.kyoto.fos.regnant.cfg.graph;

import java.util.Optional;

public class ElemCont extends Continuation {
  public final GraphElem elem;

  public ElemCont(GraphElem e) {
    this.elem = e;
  }

  @Override public Jumps getJumps() {
    return this.elem.getJumps();
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    elem.printAt(level, b);
  }

  @Override public Optional<GraphElem> elem() {
    return Optional.of(elem);
  }

  @Override public Optional<Coord> getCoord() {
    return Optional.empty();
  }
}
