package edu.kyoto.fos.regnant.simpl;

import soot.Body;
import soot.IntType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.Stmt;

import java.util.Iterator;
import java.util.List;

public class RandomRewriter {

  public static final String RANDOM_CLASS = "edu.kyoto.regnant.Random";

  // javaのrandom.nextIntをedu.kyoto.regnant.random.rand()に書き換えるメソッド
  public static Body rewriteRandom(Body b) {
    SootClass rand = Scene.v().makeSootClass(RANDOM_CLASS);
    UnitPatchingChain units = b.getUnits();
    Iterator<Unit> it = units.snapshotIterator();
    while(it.hasNext()) {
      Stmt u = (Stmt) it.next();
      if(u.containsInvokeExpr()) {
        InvokeExpr ie = u.getInvokeExpr();
        SootMethodRef mr = ie.getMethodRef();
        if(mr.getDeclaringClass().getName().equals("java.util.Random") && mr.getName().startsWith("next") && mr.getReturnType().equals(IntType.v())) {
          // replace this with a (fake) call to our nondet
          u.getInvokeExprBox().setValue(Jimple.v().newStaticInvokeExpr(
              Scene.v().makeMethodRef(
                  rand, "rand", List.of(), IntType.v(), true
              )
          ));
          continue;
        }
      }

      boolean usesRand = u.getUseBoxes().stream()
          .map(ValueBox::getValue)
          .map(Value::getType)
          .filter(RefType.class::isInstance)
          .map(RefType.class::cast)
          .map(RefType::getSootClass)
          .map(SootClass::getName)
          .anyMatch("java.util.Random"::equals);
      if(usesRand) {
        units.remove(u);
      }
    }
    return b;
  }
}
