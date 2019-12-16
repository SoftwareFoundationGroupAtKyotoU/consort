package edu.kyoto.fos.regnant.ir.expr;

public class ArrayLength extends ImpExpr implements CompoundExpr {
  private final ImpExpr arrayExpr;

  public ArrayLength(final ImpExpr arrayExpr) {
    this.arrayExpr = arrayExpr;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    this.printCompound(sb, arrayExpr);
    sb.append(".length");
  }
}
