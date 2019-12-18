package edu.kyoto.fos.regnant.simpl;

import edu.kyoto.fos.regnant.translation.Translate;
import fj.P;
import fj.P2;
import soot.Body;
import soot.Local;
import soot.RefLikeType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.CastExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class AliasInsertion {
  private static abstract class Val {
  }
  private static class FieldRef extends Val {
    public final int baseVal;
    public final SootField f;
    public FieldRef(int i, SootField f) {
      this.baseVal = i;
      this.f = f;
    }

    @Override public boolean equals(final Object o) {
      if(this == o)
        return true;
      if(o == null || getClass() != o.getClass())
        return false;
      final FieldRef fieldRef = (FieldRef) o;
      return baseVal == fieldRef.baseVal && f.equals(fieldRef.f);
    }

    @Override public int hashCode() {
      return Objects.hash(baseVal, f);
    }

    @Override public String toString() {
      return "FieldRef{" + "baseVal=" + baseVal + ", f=" + f + '}';
    }
  }
  private static class Loc extends Val {
    public final Local l;
    public Loc(Local l) {
      this.l = l;
    }

    @Override public boolean equals(final Object o) {
      if(this == o)
        return true;
      if(o == null || getClass() != o.getClass())
        return false;
      final Loc loc = (Loc) o;
      return l.equals(loc.l);
    }

    @Override public int hashCode() {
      return Objects.hash(l);
    }

    @Override public String toString() {
      return "Loc{" + "l=" + l + '}';
    }
  }
  private static class SimpleMustAliasAnalysis extends ForwardFlowAnalysis<Unit, Map<Val, Integer>> {
    public SimpleMustAliasAnalysis(final DirectedGraph<Unit> graph) {
      super(graph);
      this.doAnalysis();
    }

    // XXX: based on experience, this gets stupid big for non-trivial applications. see legato for how to do this "efficiently"
    private Map<Unit, Set<SootField>> writeSets = new HashMap<>();

    private Set<SootField> getWriteSet(Unit u) {
      return writeSets.computeIfAbsent(u, un -> {
        CallGraph cg = Scene.v().getCallGraph();
        List<SootMethod>  l = new ArrayList<>();
        cg.edgesOutOf(u).forEachRemaining(i -> l.add(i.getTgt().method()));
        ReachableMethods rm = new ReachableMethods(cg, l);
        rm.update();
        Set<SootField> writeFields = new HashSet<>();
        rm.listener().forEachRemaining(mm -> {
          if(Scene.v().isExcluded(mm.method().getDeclaringClass())) {
            return;
          }
          mm.method().retrieveActiveBody().getUnits().stream()
              .map(Unit::getDefBoxes)
              .flatMap(List::stream)
              .map(ValueBox::getValue)
              .filter(InstanceFieldRef.class::isInstance)
              .map(InstanceFieldRef.class::cast)
              .map(InstanceFieldRef::getField)
              .forEach(writeFields::add);
        });
        return writeFields;
      });
    }

    @Override protected void flowThrough(final Map<Val, Integer> in, final Unit d, final Map<Val, Integer> out) {
      out.clear();
      out.putAll(in);
      Stmt s = (Stmt) d;
      if(s.containsInvokeExpr()) {
        this.havocHeap(s, out);
      }
      if(d instanceof DefinitionStmt) {
        DefinitionStmt ds = (DefinitionStmt) d;
        Value lhs = ds.getLeftOp();
        Value rhs = ds.getRightOp();
        if(rhs instanceof CastExpr) {
          rhs = ((CastExpr) rhs).getOp();
        }
        if(lhs.getType() instanceof RefLikeType) {
          System.out.println("Modelling d " + lhs + " <- " + rhs);
          if(rhs instanceof IdentityRef) {
            assert lhs instanceof Local;
            if(rhs instanceof ThisRef) {
              out.put(new Loc((Local) lhs), this.getThisNumber());
            } else {
              assert rhs instanceof ParameterRef : rhs;
              out.put(new Loc((Local)lhs), this.getParameterNum(((ParameterRef) rhs).getIndex()));
            }
          } else {
            int newVal = this.getValueNumber(out, rhs);
            if(lhs instanceof Local) {
              out.put(new Loc((Local) lhs), newVal);
            } else if(lhs instanceof InstanceFieldRef) {
              InstanceFieldRef ifr = (InstanceFieldRef) lhs;
              Loc baseKey = new Loc((Local) ifr.getBase());
              assert out.containsKey(baseKey);
              out.put(new FieldRef(out.get(baseKey), ifr.getField()), newVal);
            } else {
              throw new RuntimeException("unsupported rhs");
            }
          }
        }
      }
    }

    private void havocHeap(final Stmt in, final Map<Val, Integer> out) {
      Set<SootField> sf = this.getWriteSet(in);
      out.replaceAll((k,v) -> {
        if(k instanceof Loc) {
          return v;
        }
        assert k instanceof FieldRef;
        if(!sf.contains(((FieldRef) k).f)) {
          return v;
        }
        return getCtxtValue(in, k, method);
      });
    }

    private int getValueNumber(Map<Val, Integer> env, final Value rhs) {
      if(rhs instanceof Local) {
        return env.get(new Loc((Local) rhs));
      } else if(rhs instanceof InstanceFieldRef) {
        InstanceFieldRef ifr = (InstanceFieldRef) rhs;
        int i = getValueNumber(env, ifr.getBase());
        return env.computeIfAbsent(new FieldRef(i, ifr.getField()), ign -> valueNumber++);
      } else {
        return rhsNumber.computeIfAbsent(rhs, ign -> valueNumber++);
      }
    }

    private Map<Value, Integer> rhsNumber = new HashMap<>();

    @Override protected Map<Val, Integer> newInitialFlow() {
      return new HashMap<>();
    }

    @Override protected void merge(final Map<Val, Integer> in1, final Map<Val, Integer> in2, final Map<Val, Integer> out) {
      // we should only use the unit one
      throw new UnsupportedOperationException();
    }

    @Override protected void merge(final Unit succNode, final Map<Val, Integer> in1, final Map<Val, Integer> in2, final Map<Val, Integer> out) {
      out.clear();
      out.putAll(in1);
      in2.forEach((k,v) -> {
        out.merge(k, v, (v1, v2) -> {
          if(Objects.equals(v1, v2)) {
            return v1;
          } else {
            return getCtxtValue(succNode, k, join);
          }
        });
      });
    }

    private Integer getCtxtValue(final Unit succNode, final Val k, final Map<Unit, Map<Val, Integer>> m) {
      return m.computeIfAbsent(succNode, ign -> new HashMap<>()).computeIfAbsent(k, ign -> valueNumber++);
    }

    private int getParameterNum(int i) {
      return -1 - i;
    }

    private int getThisNumber() {
      return 0;
    }

    private int valueNumber = 1;
    private Map<Unit, Map<Val, Integer>> join = new HashMap<>();
    private Map<Unit, Map<Val, Integer>> method = new HashMap<>();

    @Override protected void copy(final Map<Val, Integer> source, final Map<Val, Integer> dest) {
      dest.clear();
      dest.putAll(source);
    }
  }

  public static Body rewrite(final Body body) {
    System.out.println(body);
    UnitGraph ug = new BriefUnitGraph(body);
    SimpleMustAliasAnalysis mustAlias = new SimpleMustAliasAnalysis(ug);

    Map<Local, P2<InstanceFieldRef, Stmt>> singleDef = new HashMap<>();
    Map<Local, Stmt> singleUse = new HashMap<>();
    for(Unit u : body.getUnits()) {
      Stmt s = (Stmt) u;
      if(s.getDefBoxes().size() == 1 && s.getDefBoxes().get(0).getValue() instanceof Local &&
          s.containsFieldRef() && s.getFieldRef() instanceof InstanceFieldRef && s.getFieldRef().getType() instanceof RefLikeType) {
        Local defLoc = (Local) s.getDefBoxes().get(0).getValue();
        if(singleDef.containsKey(defLoc)) {
          singleDef.put(defLoc, null);
          continue;
        }
        InstanceFieldRef ifr = (InstanceFieldRef) s.getFieldRef();
        assert s.getUseBoxes().stream().map(ValueBox::getValue).anyMatch(ifr::equals);
        singleDef.put(defLoc, P.p(ifr, s));
      }
      s.getUseBoxes().stream()
          .map(ValueBox::getValue)
          .filter(Local.class::isInstance)
          .map(Local.class::cast)
          .distinct()
          .forEach(l -> {
            if(singleUse.containsKey(l)) {
              singleUse.put(l, null);
            }
            singleUse.put(l, s);
          });
    }
    SootMethodRef mrf = getAliasRef();
    singleUse.entrySet().stream().filter(kv -> singleDef.containsKey(kv.getKey())).forEach(kv -> {
      Local tempLocal = kv.getKey();
      P2<InstanceFieldRef, Stmt> src = singleDef.get(tempLocal);
      Stmt lastUse = kv.getValue();
      Map<Val, Integer> alias = mustAlias.getFlowAfter(lastUse);
      Loc defKey = new Loc(tempLocal);
      assert alias.containsKey(defKey) : defKey;
      InstanceFieldRef sourceField = src._1();
      Loc baseKey = new Loc((Local) sourceField.getBase());
      assert alias.containsKey(baseKey);
      int base = alias.get(baseKey);
      FieldRef fieldKey = new FieldRef(base, sourceField.getField());
      assert alias.containsKey(fieldKey);
      int value = alias.get(fieldKey);

      if(value == alias.get(defKey)) {
        System.out.println("Aliasing back " + tempLocal + " to " + sourceField + " defined at " + src._2());
        // yay! we can alias this back
        Jimple j = Jimple.v();
        InvokeStmt invokeStmt = j.newInvokeStmt(j.newStaticInvokeExpr(mrf, tempLocal, sourceField.getBase(), StringConstant.v(sourceField.getField().getName())));
        ug.getSuccsOf(lastUse).forEach(succ -> {
          body.getUnits().insertOnEdge(invokeStmt, lastUse, succ);
        });
      }
    });
    return body;
  }

  private static SootMethodRef getAliasRef() {
    Scene.v().setPhantomRefs(true);
    SootClass sc;
    try {
      sc = Scene.v().getSootClass(Translate.ALIASING_CLASS);
    } finally {
      Scene.v().setPhantomRefs(false);
    }
    return Scene.v().makeMethodRef(sc, "alias", List.of(
        Scene.v().getObjectType(),
        Scene.v().getObjectType(),
        Scene.v().getSootClass("java.lang.String").getType()
    ), VoidType.v(), true);
  }
}
