package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;

import java.util.function.Supplier;

public class FieldContents {
  private final Supplier<Builder> aliasBuilder;
  private final ImpExpr expr;

  public FieldContents(ImpExpr e, Supplier<Builder> aliasBuild) {
    this.expr = e;
    this.aliasBuilder = aliasBuild;
  }

  public ImpExpr getExpr() {
    return expr;
  }

  public Builder ap() {
    return aliasBuilder.get();
  }
}
