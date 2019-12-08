package edu.kyoto.fos.regnant.ir.expr;

public class IntLiteral extends ImpExpr {
  private final int value;

  public IntLiteral(int i) {
    this.value = i;
  }

  public static ImpExpr v(final int v) {
    return new IntLiteral(v);
  }

  @Override public boolean isCompound() {
    return false;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append(this.value);
  }
}
