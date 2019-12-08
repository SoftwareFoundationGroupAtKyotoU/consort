package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;

public class Assign extends Effect {
  private final String name;
  private final ImpExpr val;

  public Assign(final String name, final ImpExpr val) {
    this.name = name;
    this.val = val;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append(this.name).append(" := ");
    this.val.printOn(b);
  }
}
