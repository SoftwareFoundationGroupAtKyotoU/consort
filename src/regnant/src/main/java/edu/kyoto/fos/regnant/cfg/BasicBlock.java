package edu.kyoto.fos.regnant.cfg;

import soot.Unit;
import soot.jimple.AssignStmt;

import java.util.List;
import java.util.stream.Collectors;

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

  // // 出力するときは基本ブロックの番号と、基本ブロックのはじめと終わりの Unit しか出力しない
  // @Override public String toString() {
  //   return id + ":{" + getHead() + "->" + getTail() + "}";
  // }

  @Override public String toString() {
    String basicBlockCode;
    basicBlockCode = this.units.stream()
                    .map(unit -> unit.toString() + " (" + unit.getClass() +
                            ((unit instanceof AssignStmt)
                                    ? (" Left: " + ((AssignStmt)unit).getLeftOp().getClass().toString() + " Right: " + ((AssignStmt)unit).getRightOp().getClass().toString()) + " " + ((AssignStmt) unit).getRightOp().getType().getClass()
                                    : "") + ")")
                    .collect(Collectors.joining("\n     "));
    return "f" + id + "(){" + basicBlockCode + "}\n";
  }
}
