package edu.kyoto.fos.regnant.ir.expr;

import java.util.List;

public class Tuple extends ImpExpr implements InterleavedDo {
  private final List<ImpExpr> contents;

  public Tuple(final List<ImpExpr> tupCont) {
    this.contents = tupCont;
  }

  public static ImpExpr v(final List<ImpExpr> tupCont) {
    return new Tuple(tupCont);

  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append("(");
    this.doInterleaved(contents.stream(), sb, ImpExpr::printOn, b -> b.append(", "));
    sb.append(")");
  }

  @Override public boolean isCompound() {
    return false;
  }
}
