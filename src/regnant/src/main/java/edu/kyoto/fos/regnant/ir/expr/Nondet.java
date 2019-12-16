package edu.kyoto.fos.regnant.ir.expr;

public class Nondet extends ImpExpr {
  @Override public void printOn(final StringBuilder sb) {
    sb.append("_");
  }

  @Override public boolean isCompound() {
    return false;
  }
}
