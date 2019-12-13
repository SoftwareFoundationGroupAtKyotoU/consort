package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.translation.FlagTranslation;
import edu.kyoto.fos.regnant.translation.Translate;
import fj.data.TreeMap;
import soot.Immediate;
import soot.IntType;
import soot.Local;
import soot.SootMethod;
import soot.Type;
import soot.Value;
import soot.VoidType;
import soot.jimple.BinopExpr;
import soot.jimple.Constant;
import soot.jimple.IntConstant;
import soot.jimple.StaticInvokeExpr;
import soot.util.queue.ChunkedQueue;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public abstract class ImpExpr implements ProgFragment {
  public static ImpExpr controlFlag(final List<Integer> collect) {
    String genName = FlagTranslation.allocate(collect);
    return Call.v(
        genName, Collections.singletonList(Variable.deref(Translate.CONTROL_FLAG))
    );
  }

  public static ImpExpr callLoop(final String loopName, final List<Local> args) {
    List<ImpExpr> a = args.stream().map(Local::getName).map(Variable::immut).collect(Collectors.toList());
    return Call.v(loopName, a);
  }

  public static ImpExpr dummyValue(final Type returnType) {
    if(returnType.equals(VoidType.v()) || returnType.equals(IntType.v())) {
      return literalInt(0);
    } else {
      return NullConstant.v();
    }
  }

  public static ImpExpr var(final String tmpName) {
    return Variable.immut(tmpName);
  }

  public static ImpExpr unitValue() {
    return IntLiteral.v(0);
  }

  public static ImpExpr tuple(List<ImpExpr> tupCont) {
    return Tuple.v(tupCont);
  }

  public static String normalizeSymbol(String symbol) {
    symbol = symbol.trim();
    if(symbol.equals("==")) {
      return "=";
    } else {
      return symbol;
    }
  }

  public static ImpExpr literalInt(final int coordId) {
    return IntLiteral.v(coordId);
  }

  public static ImpExpr call(final String name, final List<ImpExpr> args) {
    return Call.v(name, args);
  }

  public abstract boolean isCompound();

  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    printOn(sb);
    return sb.toString();
  }
}
