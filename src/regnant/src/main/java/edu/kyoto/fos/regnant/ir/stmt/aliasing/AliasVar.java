package edu.kyoto.fos.regnant.ir.stmt.aliasing;

public class AliasVar extends AliasRHS {
  private final String name;

  public AliasVar(final String name) {
    this.name = name;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append(name);
  }
}
