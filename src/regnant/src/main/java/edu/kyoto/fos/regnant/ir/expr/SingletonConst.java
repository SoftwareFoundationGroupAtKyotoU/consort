package edu.kyoto.fos.regnant.ir.expr;

public abstract class SingletonConst extends ImpExpr {
  private final String sym;

  public SingletonConst(String sym) {
    this.sym = sym;
  }

  @Override public boolean isCompound() {
    return false;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append(sym);
  }
}
