package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;

public class ArrayWrite extends Effect {
  private final ImpExpr basePtr;
  private final ImpExpr ind;
  private final ImpExpr val;

  public ArrayWrite(final ImpExpr basePtr, final ImpExpr ind, final ImpExpr val) {
    this.basePtr = basePtr;
    this.ind = ind;
    this.val = val;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    this.indent(level, b);
    basePtr.printOn(b);
    b.append("[");
    ind.printOn(b);
    b.append("] <- ");
    val.printOn(b);
  }
}
