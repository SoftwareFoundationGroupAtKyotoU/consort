package edu.kyoto.fos.regnant.ir.stmt.aliasing;

public class Proj extends ApElem {
  private final int i;
  public Proj(int i) {
    this.i = i;
  }

  @Override public String extendWith(final String curr) {
    return String.format("(%s.%d)", curr, i);
  }

  @Override public String toString() {
    return "Proj{" + "i=" + i + '}';
  }
}
