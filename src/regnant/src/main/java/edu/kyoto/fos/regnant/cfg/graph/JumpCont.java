package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.AnnotatedEdge;

import java.util.Optional;

public class JumpCont extends Continuation {
  public final Jumps j;
  public final Coord c;

  public JumpCont(Coord c, Jumps j) {
    this.c = c;
    this.j = j;
  }

  @Override public Jumps getJumps() {
    return j;
  }

  public static JumpCont of(Coord c, AnnotatedEdge e) {
    return new JumpCont(c,Jumps.of(c, e));
  }

  @Override public void printAt(final int i, final StringBuilder sb) {
    indent(i, sb).append("goto: ").append(j.toString());
  }

  @Override public Optional<GraphElem> elem() {
    return Optional.empty();
  }

  @Override public Optional<Coord> getCoord() {
    return Optional.of(c);
  }
}
