package edu.kyoto.fos.regnant.ir.expr;

import java.util.List;
import java.util.stream.Collectors;

public class Call extends ImpExpr implements CompoundExpr {
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
    sb.append(this.callee);
    sb.append(this.arguments.stream().map(this::toRepr).collect(Collectors.joining(", ", "(", ")")));
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
