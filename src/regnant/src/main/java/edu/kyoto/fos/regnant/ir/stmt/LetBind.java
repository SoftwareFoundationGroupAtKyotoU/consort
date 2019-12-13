package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.expr.Mkref;

public class LetBind extends Bind {
  private String varName;
  private ImpExpr rhs;

  public LetBind(final String varName, final ImpExpr rhs, final boolean mutable) {
    this.varName = varName;
    this.rhs = mutable ? new Mkref(rhs) : rhs;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    StringBuilder sb = indent(level, b).append("let ").append(varName).append(" = ");
    this.rhs.printOn(sb);
    sb.append(" in ");
  }

  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    printAt(0, sb);
    return sb.toString();
  }

}
