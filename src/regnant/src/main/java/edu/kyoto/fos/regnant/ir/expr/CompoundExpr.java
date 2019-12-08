package edu.kyoto.fos.regnant.ir.expr;

public interface CompoundExpr {
  default void printCompound(StringBuilder sb, ImpExpr e) {
    if(e.isCompound()) {
      sb.append("(");
    }
    e.printOn(sb);
    if(e.isCompound()) {
      sb.append(")");
    }
  }
}
