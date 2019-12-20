package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;

public class Alias extends Effect {
  private final AliasOp lhs;
  private final AliasOp rhs;

  @Deprecated
  public Alias(final String lhs, final AliasOp rhs) {
    this(AliasOp.of(lhs), rhs);
  }

  public Alias(final AliasOp lhs, final AliasOp rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("alias(");
    lhs.printOn(b);
    b.append(" = ");
    rhs.printOn(b);
    b.append(")");
  }
}
