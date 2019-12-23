package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import edu.kyoto.fos.regnant.translation.ObjectModel;
import edu.kyoto.fos.regnant.translation.Translate;
import fj.data.TreeMap;
import soot.Immediate;
import soot.IntType;
import soot.Local;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.Constant;
import soot.jimple.IntConstant;
import soot.jimple.LengthExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.tagkit.IntegerConstantValueTag;
import soot.util.queue.ChunkedQueue;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kyoto.fos.regnant.ir.expr.ImpExpr.call;

public class ValueLifter {
  private final StorageLayout layout;
  private ObjectModel om;
  private final ChunkedQueue<SootMethod> queue;

  public ValueLifter(ChunkedQueue<SootMethod> workQueue, StorageLayout sl, final ObjectModel objectModel) {
    this.queue = workQueue;
    this.layout = sl;
    om = objectModel;
  }

  public ImpExpr lift(Value op, TreeMap<Local, Binding> env) {
    if(op instanceof Immediate) {
      if(op instanceof Local) {
        Local l = (Local) op;
        boolean isMutable = env.get(l).exists(Binding.MUTABLE::equals);
        if(isMutable) {
          return Variable.deref(l.getName());
        } else {
          return Variable.immut(l.getName());
        }
      } else if(op instanceof soot.jimple.NullConstant) {
        return NullConstant.v();
      } else {
        assert op instanceof Constant;
        assert op instanceof IntConstant;
        return ImpExpr.literalInt(((IntConstant) op).value);
      }
    } else if(op instanceof BinopExpr) {
      BinopExpr binopExpr = (BinopExpr) op;
      String symb = ImpExpr.normalizeSymbol(binopExpr.getSymbol());
      return new Binop(this.lift(binopExpr.getOp1(), env), symb, this.lift(binopExpr.getOp2(), env));
    } else if(op instanceof StaticInvokeExpr) {
      StaticInvokeExpr invokeExpr = (StaticInvokeExpr) op;
      SootMethod m = invokeExpr.getMethod();
      String callee = Translate.getMangledName(m);
      this.queue.add(m);
      List<ImpExpr> args = invokeExpr.getArgs().stream().map(v -> lift(v, env)).collect(Collectors.toList());
      return call(callee, args);
    } else if(op instanceof NewExpr) {
      // hoo boy
      NewExpr alloc = (NewExpr) op;
      SootClass alloced = alloc.getBaseType().getSootClass();
      // we can use Soot's numbering scheme
      int tag = alloced.getNumber();
      List<SootField> f = layout.getMetaLayout(alloced);
      List<ImpExpr> flds = Stream.concat(
          // runtime tag
          Stream.of(IntLiteral.v(tag)),
          // the initial, default values
          f.stream().map(sf -> om.allocFieldOfType(sf.getType()))).collect(Collectors.toList());
      return new Mkref(Tuple.v(flds));
    } else if(op instanceof NewArrayExpr) {
      NewArrayExpr arrayExpr = (NewArrayExpr) op;
      if(!arrayExpr.getBaseType().equals(IntType.v())) {
        throw new UnsupportedOperationException("Only supports int arrays");
      }
      return new NewArray(this.lift(arrayExpr.getSize(), env));
    } else if(op instanceof LengthExpr) {
      LengthExpr lengthExpr = (LengthExpr) op;
      return new ArrayLength(this.lift(lengthExpr.getOp(), env));
    } else if(op instanceof ArrayRef) {
      ArrayRef ref = (ArrayRef) op;
      assert ref.getType().equals(IntType.v());
      return new ArrayRead(this.lift(ref.getBase(), env), this.lift(ref.getIndex(), env));
    } else if(op instanceof StaticFieldRef) {
      StaticFieldRef sfr = (StaticFieldRef) op;
      SootField field = sfr.getField();
      if(!field.hasTag("IntegerConstantValueTag")) {
        throw new RuntimeException("Unhandled (non-constant) static field " + op);
      }
      var constTag = (IntegerConstantValueTag) field.getTag("IntegerConstantValueTag");
      return IntLiteral.v(constTag.getIntValue());
    } else {
      throw new RuntimeException("Unhandled :" + op);
    }
  }

}
