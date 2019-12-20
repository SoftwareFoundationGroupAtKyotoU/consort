package edu.kyoto.fos.regnant.ir.stmt.aliasing;

public final class Deref extends ApElem {
  private Deref() {

  }

  public static Deref v = new Deref();

  @Override public String extendWith(final String curr) {
    return String.format("(*%s)", curr);
  }

  @Override public String toString() {
    return "Deref{}";
  }
}
