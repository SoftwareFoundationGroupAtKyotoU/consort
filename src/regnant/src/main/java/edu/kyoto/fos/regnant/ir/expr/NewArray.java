package edu.kyoto.fos.regnant.ir.expr;

public class NewArray extends ImpExpr implements CompoundExpr {
  private final ImpExpr dim;
  public NewArray(final ImpExpr dim) {
    this.dim = dim;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append("mkarray ");
    this.printCompound(sb, this.dim);
  }
}
