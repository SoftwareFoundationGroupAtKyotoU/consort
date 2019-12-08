package edu.kyoto.fos.regnant.ir.expr;

public class Mkref extends ImpExpr {
  private final ImpExpr referent;

  public Mkref(ImpExpr referent) {
    this.referent = referent;
  }

  @Override public boolean isCompound() {
    return true;
  }

  @Override public void printOn(final StringBuilder sb) {
    sb.append("mkref ");
    if(this.referent.isCompound()) {
      sb.append("(");
    }
    this.referent.printOn(sb);
    if(this.referent.isCompound()) {
      sb.append(")");
    }
  }
}
