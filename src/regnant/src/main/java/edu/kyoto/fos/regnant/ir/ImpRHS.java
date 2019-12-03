package edu.kyoto.fos.regnant.ir;

import edu.kyoto.fos.regnant.storage.Binding;
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

import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class ImpRHS {
  private final Printer[] printers;

  private interface Printer extends Consumer<StringBuilder> {
  }
  private ImpRHS(Printer... printers) {
    this.printers = printers;
  }

  public static ImpRHS controlFlag(final List<Integer> collect) {
    String s = collect.stream().map(Object::toString).collect(Collectors.joining(";", "{", "}"));
    return new ImpRHS(
        string("(*%s) = %s", Translate.CONTROL_FLAG, s)
    );
  }

  public static ImpRHS call(final String loopName, final List<Local> args) {
    return new ImpRHS(
      string("%s%s", loopName, args.stream().map(Local::getName).collect(Collectors.joining(", ", "(", ")")))
    );
  }

  public static ImpRHS dummyValue(final Type returnType) {
    if(returnType.equals(VoidType.v()) || returnType.equals(IntType.v())) {
      return literalInt(0);
    } else {
      return nullConstant();
    }
  }

  private static ImpRHS nullConstant() {
    return new ImpRHS(string("null"));
  }

  public static ImpRHS var(final String tmpName) {
    return new ImpRHS(string(tmpName));
  }

  private static Printer string(String s) {
    return sb -> sb.append(s);
  }

  private static Printer string(String fmt, Object... o) {
    return string(String.format(fmt, o));
  }

  private static Printer compose(Printer... p) {
    return sb -> {
      for(final Printer printer : p) {
        printer.accept(sb);
      }
    };
  }

  public static ImpRHS unitValue() {
    return new ImpRHS(string("()"));
  }

  public static ImpRHS liftCond(final Value condition, final fj.data.TreeMap<Local, Binding> gamma) {
    return liftValue(condition, gamma);
  }

  public static ImpRHS liftValue(final Value op, final TreeMap<Local, Binding> env) {
    return new ImpRHS(innerLiftValue(op, env));
  }

  private static Printer innerLiftValue(final Value op, final TreeMap<Local, Binding> env) {
    if(op instanceof Immediate) {
      if(op instanceof Local) {
        Local l = (Local) op;
        boolean isMutable = env.get(l).exists(Binding.MUTABLE::equals);
        if(isMutable) {
          return string("(*%s)", l.getName());
        } else {
          return string(l.getName());
        }
      } else {
        assert op instanceof Constant;
        assert op instanceof IntConstant;
        return literalInt(((IntConstant) op).value).lift();
      }
    } else if(op instanceof BinopExpr) {
      BinopExpr binopExpr = (BinopExpr) op;
      return compose(
          string("("), innerLiftValue(binopExpr.getOp1(), env), string(")"),
          string(binopExpr.getSymbol()),
          string("("), innerLiftValue(binopExpr.getOp2(), env), string(")")
      );
    } else {
      throw new RuntimeException("");
    }
  }

  public static ImpRHS literalInt(final int coordId) {
    return new ImpRHS(string(String.valueOf(coordId)));
  }

  private Printer lift() {
    return this::toSyntax;
  }

  public void toSyntax(final StringBuilder indent) {
    for(final Printer printer : printers) {
      printer.accept(indent);
    }
  }
}
