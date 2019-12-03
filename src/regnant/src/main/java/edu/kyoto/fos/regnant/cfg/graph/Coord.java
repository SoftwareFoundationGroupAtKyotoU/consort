package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.Comparator;

public class Coord implements Comparable<Coord> {
  final BasicBlock src;
  final boolean cond;
  final boolean branch;

  Coord(BasicBlock b) {
    this.src = b;
    this.cond = false;
    this.branch = false;
  }

  Coord(BasicBlock b, boolean branch) {
    this.src = b;
    this.cond = true;
    this.branch = branch;
  }

  @Override public int compareTo(final Coord coord) {
    Comparator<Coord> cmp =
        Comparator
            .comparingInt(t -> t.src.getId());
    cmp = cmp.thenComparingInt(t -> t.cond ? 1 : 0).thenComparingInt(t -> t.cond ? 1 : 0);
    return cmp.compare(this, coord);
  }

  public static Coord of(boolean b, BasicBlock c) {
    return new Coord(c, b);

  }

  public static Coord of(BasicBlock c) {
    return new Coord(c);
  }
  @Override public String toString() {
    return "Coord{" + "src=" + src + ", cond=" + cond + ", branch=" + branch + '}';
  }
}
