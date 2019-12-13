package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasRHS;

public class Alias extends Effect {
  private final String lhs;
  private final AliasRHS rhs;

  public Alias(final String lhs, final AliasRHS rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("alias(").append(lhs).append(" = ");
    rhs.printOn(b);
    b.append(")");
  }
}
