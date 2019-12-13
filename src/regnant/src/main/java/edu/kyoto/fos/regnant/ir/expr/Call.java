package edu.kyoto.fos.regnant.ir.expr;

import java.util.List;

public class Call extends ImpExpr implements CompoundExpr, InterleavedDo {
  private final String callee;
  private final List<ImpExpr> arguments;

  public Call(String callee, List<ImpExpr> arguments) {
    this.callee = callee;
    this.arguments = arguments;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append(this.callee).append("(");
    this.doInterleaved(arguments.stream(), sb, ImpExpr::printOn, b -> b.append(", "));
    sb.append(")");
  }

  public static ImpExpr v(String nm, List<ImpExpr> e) {
    return new Call(nm, e);
  };

  private String toRepr(final ImpExpr impExpr) {
    StringBuilder sb = new StringBuilder();
    this.printCompound(sb, impExpr);
    return sb.toString();
  }
}
