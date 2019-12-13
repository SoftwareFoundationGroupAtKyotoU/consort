package edu.kyoto.fos.regnant.ir.stmt.aliasing;

public class Ptr extends AliasRHS {
  private final String name;

  public Ptr(final String name) {
    this.name = name;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append("*").append(name);
  }
}
