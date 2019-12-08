package edu.kyoto.fos.regnant.ir.expr;

public class UnitConstant extends SingletonConst {

  public UnitConstant() {
    super("()");
  }

  public static ImpExpr v() {
    return new UnitConstant();
  }
}
