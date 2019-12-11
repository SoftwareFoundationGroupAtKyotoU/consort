package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.expr.Variable;
import soot.Local;

import java.util.List;
import java.util.stream.Collectors;

public class Call extends Effect {
  private final ImpExpr wrapped;

  public Call(ImpExpr wrapped) {
    this.wrapped = wrapped;
  }

  public static Call loop(final String name, final List<Local> args) {
    List<ImpExpr> l = args.stream().map(Local::getName).map(Variable::immut).collect(Collectors.toList());
    return new Call(new edu.kyoto.fos.regnant.ir.expr.Call(name, l));
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b);
    wrapped.printOn(b);
  }

  public static Call of(String name, List<ImpExpr> args) {
    return new Call(ImpExpr.call(name, args));
  }
}
