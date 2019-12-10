package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.translation.FlagTranslation;
import edu.kyoto.fos.regnant.translation.Translate;
import fj.data.TreeMap;
import soot.Immediate;
import soot.IntType;
import soot.Local;
import soot.Type;
import soot.Value;
import soot.VoidType;
import soot.jimple.BinopExpr;
import soot.jimple.Constant;
import soot.jimple.IntConstant;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public abstract class ImpExpr {
  public static ImpExpr controlFlag(final List<Integer> collect) {
    String genName = FlagTranslation.allocate(collect);
    return Call.v(
        genName, Collections.singletonList(Variable.deref(Translate.CONTROL_FLAG))
    );
  }

  public static ImpExpr call(final String loopName, final List<Local> args) {
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

  public static ImpExpr liftCond(final Value condition, final fj.data.TreeMap<Local, Binding> gamma) {
    return liftValue(condition, gamma);
  }

  public static ImpExpr liftValue(final Value op, final TreeMap<Local, Binding> env) {
    if(op instanceof Immediate) {
      if(op instanceof Local) {
        Local l = (Local) op;
        boolean isMutable = env.get(l).exists(Binding.MUTABLE::equals);
        if(isMutable) {
          return Variable.deref(l.getName());
        } else {
          return Variable.immut(l.getName());
        }
      } else {
        assert op instanceof Constant;
        assert op instanceof IntConstant;
        return literalInt(((IntConstant) op).value);
      }
    } else if(op instanceof BinopExpr) {
      BinopExpr binopExpr = (BinopExpr) op;
      return new Binop(
          liftValue(binopExpr.getOp1(), env),
          binopExpr.getSymbol(),
          liftValue(binopExpr.getOp2(), env)
      );
    } else {
      throw new RuntimeException("Unhandled :" + op);
    }
  }

  public static ImpExpr literalInt(final int coordId) {
    return IntLiteral.v(coordId);
  }

  public abstract boolean isCompound();
  public abstract void printOn(StringBuilder sb);

  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    printOn(sb);
    return sb.toString();
  }
}
