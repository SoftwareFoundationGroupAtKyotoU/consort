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

public abstract class ImpExpr {
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

  public static ImpExpr liftCall(final String loopName, final List<Value> args, TreeMap<Local, Binding> gamma, final ChunkedQueue<SootMethod> q) {
    List<ImpExpr> a = args.stream().map(v -> liftValue(v, gamma, q)).collect(Collectors.toList());
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

  public static ImpExpr liftCond(final Value condition, final TreeMap<Local, Binding> gamma, final ChunkedQueue<SootMethod> q) {
    return liftValue(condition, gamma, q);
  }

  public static ImpExpr liftValue(final Value op, final TreeMap<Local, Binding> env, final ChunkedQueue<SootMethod> q) {
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
      String symb = normalizeSymbol(binopExpr.getSymbol());
      return new Binop(liftValue(binopExpr.getOp1(), env, q), symb, liftValue(binopExpr.getOp2(), env, q));
    } else if(op instanceof StaticInvokeExpr) {
      StaticInvokeExpr invokeExpr = (StaticInvokeExpr) op;
      SootMethod m = invokeExpr.getMethod();
      String callee = Translate.getMangledName(m);
      q.add(m);
      List<ImpExpr> args = invokeExpr.getArgs().stream().map(v -> liftValue(v, env, q)).collect(Collectors.toList());
      return call(callee, args);
    } else {
      throw new RuntimeException("Unhandled :" + op);
    }
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
  public abstract void printOn(StringBuilder sb);

  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    printOn(sb);
    return sb.toString();
  }
}
