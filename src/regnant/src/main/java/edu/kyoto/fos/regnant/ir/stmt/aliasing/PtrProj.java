package edu.kyoto.fos.regnant.ir.stmt.aliasing;

public class PtrProj extends AliasRHS {
  private final int proj;
  private final String ptr;

  public PtrProj(final String fieldBase, final int slot) {
    this.ptr = fieldBase;
    this.proj = slot;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append("(*").append(ptr).append(").").append(this.proj);
  }
}
