package edu.kyoto.fos.regnant.ir.expr;

public class Binop extends ImpExpr implements CompoundExpr {
  private final ImpExpr rhs;
  private final ImpExpr lhs;
  private final String sym;

  public Binop(ImpExpr lhs, String sym, ImpExpr rhs) {
    this.lhs = lhs;
    this.sym = sym.trim();
    this.rhs = rhs;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    this.printCompound(sb, this.lhs);
    sb.append(" ").append(this.sym).append(" ");
    this.printCompound(sb, this.rhs);
  }
}
