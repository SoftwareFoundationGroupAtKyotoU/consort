package edu.kyoto.fos.regnant.ir;

import edu.kyoto.fos.regnant.Printable;

public class Bind implements Printable {
  private String varName;
  private ImpRHS rhs;
  private boolean mutable;

  public Bind(final String varName, final ImpRHS rhs, final boolean mutable) {
    this.varName = varName;
    this.rhs = rhs;
    this.mutable = mutable;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    StringBuilder sb = indent(level, b).append("let ").append(varName).append(" = ");
    if(this.mutable) {
      sb.append("mkref (");
    } else {
      sb.append("(");
    }
    this.rhs.toSyntax(sb);
    sb.append(") in ");
  }

  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    printAt(0, sb);
    return sb.toString();
  }
}
