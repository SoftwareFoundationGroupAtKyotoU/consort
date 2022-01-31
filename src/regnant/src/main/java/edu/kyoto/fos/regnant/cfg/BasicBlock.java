package edu.kyoto.fos.regnant.cfg;

import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;

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

  private static String showDetail(Unit unit) {
    String s;

    if (unit instanceof AssignStmt) {
      s = unit + " (" + unit.getClass() + (" Left: " + ((AssignStmt)unit).getLeftOp().getClass().toString()
              + " Right: " + ((AssignStmt)unit).getRightOp().getClass().toString()) + " "
              + ((AssignStmt) unit).getRightOp().getType().getClass() + ")";
    } else if (unit instanceof IdentityStmt) {
      s = unit + " (" + unit.getClass() + (" Left: " + ((IdentityStmt)unit).getLeftOp().getClass().toString()
              + " Right: " + ((IdentityStmt)unit).getRightOp().getClass().toString()) + " "
              + ((IdentityStmt) unit).getRightOp().getType().getClass() + ")";
    } else {
      s = unit + " (" + unit.getClass() + ")";
    }

    return s;
  }

  @Override public String toString() {
    String basicBlockCode;
    basicBlockCode = this.units.stream()
                    .map(BasicBlock::showDetail)
                    .collect(Collectors.joining("\n     "));
    return "f" + id + "(){" + basicBlockCode + "}\n";
  }
}
