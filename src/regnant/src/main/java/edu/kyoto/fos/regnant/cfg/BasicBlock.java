package edu.kyoto.fos.regnant.cfg;

import soot.Unit;

import java.util.List;

public final class BasicBlock implements Comparable<BasicBlock> {
  public static int idCounter = 0;
  public final int id = idCounter++;

  public final List<Unit> units;

  public BasicBlock(List<Unit> units) {
    this.units = units;
  }

  public Unit getTail() {
    return units.get(units.size() - 1);
  }

  public Unit getHead() {
    return units.get(0);
  }

  public int getId() {
    return id;
  }

  @Override public boolean equals(final Object o) {
    if(o == null) {
      return false;
    }
    if(!(o instanceof BasicBlock)) {
      return false;
    }
    return this.id == ((BasicBlock) o).id;
  }

  @Override public int hashCode() {
    return id;
  }

  @Override public int compareTo(final BasicBlock basicBlock) {
    return this.getId() - basicBlock.getId();
  }

  @Override public String toString() {
    return id + ":{" + getHead() + "->" + getTail() + "}";
  }
}
