package edu.kyoto.fos.regnant.ir.expr;

public class Variable extends ImpExpr {
  private final boolean isDeref;
  private final String name;

  public Variable(String nm, boolean isDeref) {
    this.name = nm;
    this.isDeref = isDeref;
  }

  @Override public boolean isCompound() {
    return this.isDeref;
  }

  @Override public void printOn(final StringBuilder sb) {
    if(this.isDeref) {
      sb.append("*").append(this.name);
    } else {
      sb.append(name);
    }
  }

  public static ImpExpr deref(String var) {
    return new Variable(var, true);
  }

  public static ImpExpr immut(String var) {
    return new Variable(var, false);
  }
}
