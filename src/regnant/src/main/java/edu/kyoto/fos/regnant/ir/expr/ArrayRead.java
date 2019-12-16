package edu.kyoto.fos.regnant.ir.expr;

public class ArrayRead extends ImpExpr {

  private final ImpExpr arrayExpr, indExpr;

  public ArrayRead(final ImpExpr arrayExpr, final ImpExpr indExpr) {
    this.arrayExpr = arrayExpr;
    this.indExpr = indExpr;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    this.arrayExpr.printOn(sb);
    sb.append("[");
    this.indExpr.printOn(sb);
    sb.append("]");
  }
}
