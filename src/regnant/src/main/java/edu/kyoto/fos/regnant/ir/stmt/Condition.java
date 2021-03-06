package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.ir.expr.ImpExpr;

public class Condition extends Effect {
  private final ImpExpr cond;
  private final Printable tBranch;
  private final Printable fBranch;

  public Condition(ImpExpr cond, Printable tBranch, Printable fBranch) {
    this.cond = cond;
    this.tBranch = tBranch;
    this.fBranch = fBranch;
  }
  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("if ");
    cond.printOn(b);
    b.append(" then\n");
    tBranch.printAt(level + 1, b);
    b.append("\n");
    indent(level, b).append("else\n");
    fBranch.printAt(level + 1, b);
  }
}
