package edu.kyoto.fos.regnant.simpl;

import edu.kyoto.fos.regnant.translation.UnreachableTag;
import soot.Body;
import soot.Local;
import soot.PatchingChain;
import soot.SootClass;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.NeExpr;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.internal.JNopStmt;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.function.Consumer;

public class AssertionRewriter {
  public static Body rewrite(final Body b) {
    b.getLocals().forEach(l -> {
      if(l.getName().startsWith("$")) {
        l.setName(l.getName().replaceFirst("\\$", "_tmp_"));
      }
    });

    SootClass declaringClass = b.getMethod().getDeclaringClass();
    PatchingChain<Unit> u = b.getUnits();
    LinkedList<Unit> worklist = new LinkedList<>();
    worklist.add(u.getFirst());
    Set<Unit> visited = new HashSet<>();
    while(!worklist.isEmpty()) {
      Unit it = worklist.removeFirst();
      if(it == null) {
        continue;
      }
      if(!visited.add(it)) {
        continue;
      }
      // is this particularly robust? No
      if(it instanceof AssignStmt) {
        AssignStmt assignStmt = (AssignStmt) it;
        if(assignStmt.getRightOp() instanceof StaticFieldRef) {
          StaticFieldRef sf = (StaticFieldRef) assignStmt.getRightOp();
          if(sf.getField().getDeclaringClass().equals(declaringClass) && sf.getField().getName().equals("$assertionsDisabled")) {
            rewriteAssertionBlock(assignStmt, u, worklist, visited);
            continue;
          }
        }
      }
      worklist.add(u.getSuccOf(it));
    }

    return b;
  }

  private static void rewriteAssertionBlock(final AssignStmt it, final PatchingChain<Unit> u, final LinkedList<Unit> worklist, final Set<Unit> visited) {
    Consumer<Unit> removal = unit -> {
      visited.add(unit);
      u.remove(unit);
    };
    assert it.getLeftOp() instanceof Local;
    Local jumpLocal = (Local) it.getLeftOp();
    assert u.getSuccOf(it) instanceof IfStmt;
    IfStmt branch = (IfStmt) u.getSuccOf(it);

    // remove the read
    removal.accept(it);
    Value v = branch.getCondition();
    assert v instanceof NeExpr;
    NeExpr ne = (NeExpr) v;

    assert ne.getOp1().equals(jumpLocal);
    assert ne.getOp2().equals(IntConstant.v(0));

    // this is where we jump when assertions are disabled (i.e., the assertions disabled flag is not false)
    Unit succBlock = branch.getTarget();
    worklist.add(succBlock);

    Unit assertBlock = u.getSuccOf(branch);

    removal.accept(branch);
    rewriteAssertionBlock(succBlock, assertBlock, u, removal);
  }

  private static void rewriteAssertionBlock(Unit stop, final Unit assertBlock, final PatchingChain<Unit> u, final Consumer<Unit> removal) {
    // all assertions should (must?) be straightline code
    Unit it = assertBlock;
    while(!it.equals(stop)) {
      if(it instanceof AssignStmt && ((AssignStmt) it).getRightOp() instanceof NewExpr) {
        NewExpr newExpr = (NewExpr) ((AssignStmt) it).getRightOp();
        if(newExpr.getBaseType().getSootClass().getName().equals("java.lang.AssertionError")) {
          // this should be an assert false
          Stmt d = new JNopStmt();
          d.addTag(new UnreachableTag());
          Unit removeIt = u.getSuccOf(it);
          u.swapWith(it, d);
          it = d;
          while(true) {
            if(removeIt instanceof ThrowStmt) {
              removal.accept(removeIt);
              break;
            } else {
              Unit nxt = u.getSuccOf(removeIt);
              removal.accept(removeIt);
              removeIt = nxt;
            }
          }
        }
      }
      it = u.getSuccOf(it);
    }
  }
}
