package edu.kyoto.fos.regnant.ir.expr;

public class NullConstant extends SingletonConst {
  public NullConstant() {
    super("null");
  }

  public static ImpExpr v() {
    return new NullConstant();
  }
}
