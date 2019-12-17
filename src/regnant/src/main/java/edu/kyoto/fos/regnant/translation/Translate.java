package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.cfg.graph.BlockSequence;
import edu.kyoto.fos.regnant.cfg.graph.ConditionalNode;
import edu.kyoto.fos.regnant.cfg.graph.Continuation;
import edu.kyoto.fos.regnant.cfg.graph.Coord;
import edu.kyoto.fos.regnant.cfg.graph.ElemCont;
import edu.kyoto.fos.regnant.cfg.graph.GraphElem;
import edu.kyoto.fos.regnant.cfg.graph.InstNode;
import edu.kyoto.fos.regnant.cfg.graph.JumpCont;
import edu.kyoto.fos.regnant.cfg.graph.JumpNode;
import edu.kyoto.fos.regnant.cfg.graph.LoopNode;
import edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation;
import edu.kyoto.fos.regnant.ir.expr.ArrayLength;
import edu.kyoto.fos.regnant.ir.expr.ArrayRead;
import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.expr.ValueLifter;
import edu.kyoto.fos.regnant.ir.expr.Variable;
import edu.kyoto.fos.regnant.simpl.RandomRewriter;
import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.storage.LetBindAllocator;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import fj.Ord;
import fj.P;
import fj.P2;
import fj.data.Option;
import fj.data.TreeMap;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.PointsToAnalysis;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LengthExpr;
import soot.jimple.NopStmt;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.VirtualCalls;
import soot.util.NumberedString;
import soot.util.Numberer;
import soot.util.queue.ChunkedQueue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation.*;

public class Translate {
  private static final String THIS_PARAM = "reg$this_in";
  private final FlagInstrumentation flg;
  private final Body b;
  private final LetBindAllocator alloc;
  private final InstructionStream stream;
  private final ChunkedQueue<SootMethod> worklist;
  private final StorageLayout layout;
  private final ValueLifter lifter;
  private int coordCounter = 1;
  private Map<Coord, Integer> coordAssignment = new HashMap<>();
  public static final String CONTROL_FLAG = "reg$control";

  public Translate(Body b, GraphElem startElem, FlagInstrumentation flg, LetBindAllocator alloc, final ChunkedQueue<SootMethod> worklist, StorageLayout sl) {
    this.flg = flg;
    this.b = b;
    this.alloc = alloc;
    this.worklist = worklist;
    this.layout = sl;
    this.lifter = new ValueLifter(worklist, layout);
    this.stream = InstructionStream.fresh("main", l -> {
      Env e = Env.empty();
      if(flg.setFlag.size() > 0) {
        l.addBinding(CONTROL_FLAG, ImpExpr.literalInt(0), true);
        e = e.updateBound(Collections.singletonMap(new JimpleLocal(CONTROL_FLAG, IntType.v()), Binding.MUTABLE));
      }
      translateElem(l, startElem, e);
    });
    this.stream.close();
  }

  public StringBuilder print() {
    StringBuilder sb = new StringBuilder();
    this.stream.sideFunctions.forEach(p -> {
      List<String> argNames = p._2();
      sb.append(p._3().dumpAs(p._1(), argNames));
    });
    List<String> params = new ArrayList<>();
    if(!this.b.getMethod().isStatic()) {
      params.add(THIS_PARAM);
    }
    for(int i = 0; i < this.b.getMethod().getParameterCount(); i++) {
      params.add(this.getParamName(i));
    }

    sb.append(this.stream.dumpAs(this.getMangledName(), params));
    return sb;
  }

  public void printOn(Appendable app) throws IOException {
    app.append(this.print());
  }


  protected static class Env {
    final fj.data.TreeMap<Local, Binding> boundVars;
    final boolean inLoop;
    final P2<String, List<Local>> currentLoop;

    Env(final boolean inLoop, final TreeMap<Local, Binding> boundVars, final P2<String, List<Local>> currentLoop) {
      this.boundVars = boundVars;
      this.inLoop = inLoop;
      this.currentLoop = currentLoop;
    }

    public Env enterLoop(String nm, List<Local> locs) {
      return new Env(true, boundVars, P.p(nm, locs));
    }

    public Env updateBound(Map<Local, Binding> b) {
      TreeMap<Local, Binding> newBind = fj.data.Stream.iterableStream(b.entrySet()).foldLeft((curr, elem) ->
          curr.set(elem.getKey(), elem.getValue()), boundVars);
      return new Env(inLoop, newBind, currentLoop);
    }

    public static Env empty() {
      return new Env(false, fj.data.TreeMap.empty(Ord.ord(l1 -> l2 ->
          Ord.intOrd.compare(l1.getNumber(), l2.getNumber()))), null);
    }
  }

  @SuppressWarnings("unchecked") private Env translateElem(InstructionStream outStream, GraphElem elem, Env e) {
    Map<String, Object> annot = elem.getAnnot();
    if(annot.containsKey(GATE_ON)) {
      Set<Coord> cond = elem.getAnnotation(GATE_ON, Set.class);
      InstructionStream i = InstructionStream.fresh("gate-top");
      translateElemChoose(i, elem, e);
      outStream.addCond(
          ImpExpr.controlFlag(cond.stream().map(this::getCoordId).collect(Collectors.toList())),
          i.andClose(),
          InstructionStream.unit("gate"));
      return e;
    } else {
      return translateElemChoose(outStream, elem, e);
    }
  }

  @SuppressWarnings("unchecked")
  private Env translateElemChoose(final InstructionStream i, final GraphElem elem, Env e) {
    if(elem.getAnnot().containsKey(CHOOSE_BY)) {
      assert elem instanceof InstNode;
      InstNode inst = (InstNode) elem;
      Map<BasicBlock, Set<Coord>> chooseBy = elem.getAnnotation(CHOOSE_BY, Map.class);
      assert chooseBy.size() > 1;
      assert chooseBy.size() == inst.hds.size();
      translateElemChoose(i, inst.hds.iterator(), chooseBy, e);
      return e;
    } else {
      return translateElemLoop(i, elem, e);
    }
  }

  private void translateElemChoose(final InstructionStream i,
      final Iterator<GraphElem> iterator,
      final Map<BasicBlock,Set<Coord>> chooseBy, Env e) {
    assert iterator.hasNext();
    GraphElem hd = iterator.next();
    if(!iterator.hasNext()) {
      translateElemLoop(i, hd, e);
    } else {
      List<Integer> choiceBy = toChoiceFlags(chooseBy.get(hd.getHead()));
      InstructionStream curr = InstructionStream.fresh("choice1");
      InstructionStream rest = InstructionStream.fresh("choice-rest");
      translateElemLoop(curr, hd, e);
      curr.close();
      translateElemChoose(rest, iterator, chooseBy, e);
      i.addCond(ImpExpr.controlFlag(choiceBy), curr, rest.andClose());
    }
  }

  private List<Integer> toChoiceFlags(final Set<Coord> tmp) {
    return tmp.stream().map(this::getCoordId).collect(Collectors.toList());
  }

  @SuppressWarnings("unchecked")
  private Env translateElemLoop(final InstructionStream i, final GraphElem elem, Env e) {
    if(elem.isLoop()) {
      Map<String, Object> annot = elem.getAnnot();
      String loopName = this.getLoopName(elem);
      List<Local> args = new ArrayList<>();
      e.boundVars.keys().forEach(args::add);

      InstructionStream lBody = InstructionStream.fresh("loop-body");
      translateElemBase(lBody, elem, e.enterLoop(loopName, args));
      lBody.close();
      assert lBody.isTerminal();
      i.addSideFunction(loopName, args, lBody);

      i.addLoopInvoke(loopName, args);
      List<P2<List<Integer>, InstructionStream>> doIf = new ArrayList<>();
      if(annot.containsKey(RECURSE_ON) && !elem.getAnnotation(RECURSE_ON,Set.class).isEmpty()) {
        assert e.currentLoop != null;
        Set<Coord> recFlags = elem.getAnnotation(RECURSE_ON, Set.class);
        InstructionStream l = InstructionStream.fresh("recurse-gate");
        l.ret(ImpExpr.callLoop(e.currentLoop._1(), e.currentLoop._2()));
        List<Integer> gateOn = toChoiceFlags(recFlags);
        doIf.add(P.p(gateOn, l));
      }
      if(annot.containsKey(RETURN_ON) && !elem.getAnnotation(RETURN_ON,Set.class).isEmpty()) {
        ImpExpr toReturn = ImpExpr.unitValue();
        InstructionStream l = InstructionStream.fresh("return-gate");
        l.ret(toReturn);
        List<Integer> gateOn = toChoiceFlags(elem.getAnnotation(RETURN_ON, Set.class));
        doIf.add(P.p(gateOn, l));
      }
      if(doIf.size() > 0) {
        gateLoop(i, doIf.iterator());
      }
      return e;
    } else {
      return translateElemBase(i, elem, e);
    }
  }

  private void gateLoop(InstructionStream tgt,
      Iterator<P2<List<Integer>, InstructionStream>> instStream) {
    gateLoop(tgt, instStream, ImpExpr::controlFlag, InstructionStream::close);
  }

  private void gateLoop(final InstructionStream tgt,
      final Iterator<P2<List<Integer>,InstructionStream>> instStream,
      final Function<List<Integer>,ImpExpr> cond,
      final Consumer<InstructionStream> fallThrough) {
    P2<List<Integer>, InstructionStream> g = instStream.next();
    final InstructionStream elseBranch;
    if(instStream.hasNext()) {
      elseBranch = InstructionStream.fresh("gate-choice", l -> gateLoop(l, instStream, cond, fallThrough));
      elseBranch.close();
    } else {
      elseBranch = InstructionStream.fresh("fallthrough", fallThrough);
    }
    tgt.addCond(cond.apply(g._1()), g._2(), elseBranch);

  }

  private String getMangledName() {
    SootMethod m = this.b.getMethod();
    return getMangledName(m);
  }

  public static String getMangledName(final SootMethod m) {
    return m.getDeclaringClass() + "_" + m.getName();
  }

  private String getLoopName(final GraphElem elem) {
    return String.format("_consort_%s_%s__loop_%d",
        b.getMethod().getDeclaringClass().getName(),
        b.getMethod().getName(),
        elem.getHead().id);
  }

  private InstructionStream compileJump(Continuation c, final Env env) {
    if(c instanceof JumpCont) {
      JumpCont jumpCont = (JumpCont) c;
      Coord srcCoord = jumpCont.c;
      if(flg.setFlag.contains(srcCoord) || flg.returnJump.contains(srcCoord) || jumpCont.j.cont.size() > 0) {
        return InstructionStream.fresh("jump", i -> jumpFrom(jumpCont.c, i, env));
      } else {
        return InstructionStream.unit("fallthrough");
      }
    } else {
      assert c instanceof ElemCont;
      return InstructionStream.fresh("branch", l -> translateElem(l, ((ElemCont) c).elem, env));
    }
  }

  private void jumpFrom(final Coord c, final InstructionStream i, Env e) {
    if(flg.recurseFlag.contains(c)) {
      i.ret(ImpExpr.callLoop(e.currentLoop._1(), e.currentLoop._2()));
      assert !flg.setFlag.contains(c) && !flg.returnJump.contains(c);
    }
    if(flg.setFlag.contains(c)) {
      assert !i.isTerminal();
      i.setControl(this.getCoordId(c));
    }
    if(flg.returnJump.contains(c)) {
      assert !i.isTerminal();
      i.returnUnit();
    }
  }

  private Env translateElemBase(final InstructionStream lBody, final GraphElem elem, final Env env) {
    // we would have gated this already
    assert !(elem instanceof InstNode);
    if(elem instanceof ConditionalNode) {
      ConditionalNode cond = (ConditionalNode) elem;
      return encodeBasicBlock(cond.head, lBody, u -> {
        assert u instanceof IfStmt; return ((IfStmt)u);
      }, (env_, el) -> {
        ImpExpr path = lifter.lift(el.getCondition(), env_.boundVars);
        lBody.addCond(path,
            compileJump(cond.tBranch, env_).andClose(), compileJump(cond.fBranch, env_).andClose());
      }, env);
    } else if(elem instanceof JumpNode) {
      JumpNode j = (JumpNode) elem;
      return encodeBasicBlock(j.head, lBody, u -> (u instanceof ReturnStmt || u instanceof ReturnVoidStmt) ? u : null, (env_, rs_) -> {
        Coord c = Coord.of(j.head);
        if(rs_ instanceof ReturnStmt) {
          ReturnStmt rs = (ReturnStmt) rs_;
          if(flg.setFlag.contains(c)) {
            lBody.setControl(this.getCoordId(c));
          }
          addParameterAliasing(env_, lBody);
          lBody.ret(lifter.lift(rs.getOp(), env_.boundVars));
          return;
        } else if(rs_ instanceof ReturnVoidStmt) {
          if(flg.setFlag.contains(c)) {
            lBody.setControl(this.getCoordId(c));
          }
          addParameterAliasing(env_, lBody);
          lBody.returnUnit();
          return;
        }
        jumpFrom(c, lBody, env_);
      }, env);
    } else if(elem instanceof BlockSequence) {
      BlockSequence sequence = (BlockSequence) elem;
      Env it = env;
      LinkedList<GraphElem> list = new LinkedList<>(sequence.chain);
      while(!list.isEmpty()) {
        GraphElem hd = list.pop();
        it = translateElem(lBody, hd, it);
      }
    } else if(elem instanceof LoopNode) {
      return this.translateElemBase(lBody, ((LoopNode) elem).loopBody, env);
    }
    return env;
  }

  private void addParameterAliasing(final Env env_, final InstructionStream lBody) {
    List<Type> paramTypes = this.b.getMethod().getParameterTypes();
    for(int i = 0; i < paramTypes.size(); i++) {
      Type t = paramTypes.get(i);
      if(!(t instanceof RefLikeType)) {
        continue;
      }
      Local l = this.b.getParameterLocal(i);
      Option<Binding> storage = env_.boundVars.get(l);
      assert storage.isSome();
      if(storage.some() == Binding.CONST) {
        // alias it back
        lBody.addAlias(l.getName(), this.getParamName(i));
      }
    }
    if(!this.b.getMethod().isStatic()) {
      Local l = this.b.getThisLocal();
      Binding bind = env_.boundVars.get(l).some();
      if(bind == Binding.CONST) {
        lBody.addAlias(l.getName(), THIS_PARAM);
      }
    }
  }

  private void encodeInstruction(final InstructionStream str, final Unit unit,
      final Set<Local> needDefine,
      fj.data.TreeMap<Local, Binding> env) {
    assert !(unit instanceof IfStmt);
    assert !(unit instanceof ReturnStmt);
    if(unit instanceof NopStmt) {
      if(unit.hasTag(UnreachableTag.NAME)) {
        str.addAssertFalse();
      }
    } else if(unit instanceof ThrowStmt) {
      throw new RuntimeException("not handled yet");
    } else if(unit instanceof IdentityStmt) {
      IdentityStmt identityStmt = (IdentityStmt) unit;
      Value rhs = identityStmt.getRightOp();
      assert rhs instanceof IdentityRef;

      assert identityStmt.getLeftOp() instanceof Local;
      Local defn = (Local) identityStmt.getLeftOp();
      assert needDefine.contains(defn);
      assert env.contains(defn);
      needDefine.remove(defn);
      // hahaha oo later
      boolean mutableParam = env.get(defn).some() == Binding.MUTABLE;
      if(rhs instanceof ThisRef) {
        str.addBinding(defn.getName(), ImpExpr.var(THIS_PARAM), mutableParam);
      } else {
        assert rhs instanceof ParameterRef;
        int paramNumber = ((ParameterRef) rhs).getIndex();
        str.addBinding(defn.getName(), ImpExpr.var(this.getParamName(paramNumber)), mutableParam);
      }
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof Local) {
      AssignStmt as = (AssignStmt) unit;
      Value lhs = as.getLeftOp();
      Local target = (Local) lhs;
      boolean needsDefinition = needDefine.contains(target);
      needDefine.remove(target);
      boolean mutableBinding = env.get(target).some() == Binding.MUTABLE;
      InstructionStream writeStream;
      if(!needsDefinition) {
        writeStream = InstructionStream.fresh("write");
      } else {
        writeStream = str;
      }
      LocalContents c = this.liftValue(unit, as.getRightOp(), new LocalWrite(unit), writeStream, -1, BindMode.INTRAPROC, env);
      if(needsDefinition) {
        writeStream.addBinding(target.getName(), c.getValue(), mutableBinding);
      } else {
        writeStream.addWrite(target.getName(), c.getValue());
      }
      c.cleanup(writeStream);
      if(!needsDefinition) {
        str.addBlock(writeStream);
      }
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof InstanceFieldRef) {
      AssignStmt assign = (AssignStmt) unit;
      ImpExpr right = lifter.lift(assign.getRightOp(), env);
      InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getLeftOp();
      this.writeField(str, fieldRef, env, right);
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof ArrayRef) {
      ArrayRef arrayRef = (ArrayRef) ((AssignStmt) unit).getLeftOp();
      InstructionStream s = InstructionStream.fresh("array");
      LocalContents basePtr = this.unwrapArray(arrayRef, s, env, new FieldOpWrite("array"), -1);
      ImpExpr ind = this.lifter.lift(arrayRef.getIndex(), env);
      ImpExpr val = this.lifter.lift(((AssignStmt) unit).getRightOp(), env);
      s.addArrayWrite(basePtr.getValue(), ind, val);
      basePtr.cleanup(s);
      str.addBlock(s);
    } else if(unit instanceof InvokeStmt && ((InvokeStmt) unit).getInvokeExpr() instanceof SpecialInvokeExpr && ((InvokeStmt) unit).getInvokeExpr().getMethodRef().getName().equals("<init>")) {
      // we don't do constructors here
      // TODO: this should skip the *object* constructor, not all super class constructors...
      // do nothing!
    } else if(unit instanceof InvokeStmt) {
      InstructionStream call = InstructionStream.fresh("call");
      LocalContents c = this.translateCall(unit, call, ((InvokeStmt) unit).getInvokeExpr(), env);
      call.addExpr(c.getValue());
      c.cleanup(call);
      str.addBlock(call);
    } else if(!(unit instanceof GotoStmt)) {
      // this is really hard, do it later
      throw new RuntimeException("Unhandled statement " + unit + " " + unit.getClass());
    }
  }

  private void writeField(InstructionStream str, InstanceFieldRef fieldRef, TreeMap<Local, Binding> env, ImpExpr lhs) {
    InstructionStream i = InstructionStream.fresh("write", l -> {
      FieldPointer p = unwrapField(l, fieldRef, env, new FieldOpWrite("field"));
      l.addWrite(p.fieldName, lhs);
      p.cleanup(l);
    });
    i.close();
    str.addBlock(i);
  }

  private LocalContents translateCall(Unit ctxt, InstructionStream str, InvokeExpr expr, final TreeMap<Local, Binding> env) {
    if(isRegnantIntrinsic(expr)) {
      return this.handleIntrinsic(str, expr);
    }
    final VarManager vm = new BindCall(ctxt);
    List<LocalContents> args = new ArrayList<>();
    String callee;
    List<Value> v = expr.getArgs();
    if(expr instanceof StaticInvokeExpr) {
      callee = getMangledName(expr.getMethod());
      worklist.add(expr.getMethod());
    } else if(expr instanceof SpecialInvokeExpr) {
      SootMethod m = expr.getMethod();
      worklist.add(m);
      callee = getMangledName(m);
    } else {
      assert expr instanceof VirtualInvokeExpr;
      // Points to analysis time!
      VirtualInvokeExpr inv = (VirtualInvokeExpr) expr;
      Local l = (Local) inv.getBase();
      PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
      NumberedString subSig = expr.getMethodRef().getSubSignature();
      Map<SootMethod, Set<SootClass>> callees =
          pta.reachingObjects(l).possibleTypes().stream()
              .filter(RefType.class::isInstance)
              .map(RefType.class::cast)
              .collect(Collectors
                  .groupingBy(refTy -> VirtualCalls.v().resolveNonSpecial(refTy, subSig, false),
                      Collectors.mapping(RefType::getSootClass, Collectors.toSet())));
      if(callees.size() == 1) {
        SootMethod m = callees.keySet().iterator().next();
        callee = getMangledName(m);
        worklist.add(m);
      } else {
        // de-virtualize
        callee = devirtualize(ctxt, str, callees);
      }
    }
    if(expr instanceof InstanceInvokeExpr) {
      InstanceInvokeExpr iie = (InstanceInvokeExpr) expr;
      args.add(liftValue(ctxt, iie.getBase(), vm, str, 0, BindMode.INTERPROC, env));
    }
    for(int i = 0; i < v.size(); i++) {
      Value a = v.get(i);
      int slot = i + 1;
      var lifted = liftValue(ctxt, a, vm, str, slot, BindMode.INTERPROC, env);
      args.add(lifted);
    }
    ImpExpr call = ImpExpr.call(callee, args.stream().map(LocalContents::getValue).collect(Collectors.toList()));
    return new CompoundCleanup(call, args.stream());
  }

  private LocalContents handleIntrinsic(final InstructionStream str, final InvokeExpr expr) {
    assert expr.getMethodRef().getName().equals("rand");
    return new SimpleContents(ImpExpr.nondet());
  }

  private boolean isRegnantIntrinsic(final InvokeExpr expr) {
    return expr instanceof StaticInvokeExpr &&
        (expr.getMethodRef().getDeclaringClass().getName().equals(RandomRewriter.RANDOM_CLASS) && expr.getMethodRef().getName().equals("rand"));
  }

  private String devirtualize(final Unit u, final InstructionStream s, final Map<SootMethod,Set<SootClass>> callees) {
    assert callees.size() > 1;
    Numberer<Unit> numberer = Scene.v().getUnitNumberer();
    numberer.add(u);
    long l = numberer.get(u);

    assert layout.haveSameRepr(callees.values().stream().flatMap(Set::stream));
    SootMethod repr = callees.keySet().iterator().next();
    assert callees.keySet().stream().allMatch(m -> m.getParameterCount() == repr.getParameterCount());
    assert callees.keySet().stream().noneMatch(SootMethod::isStatic);


    String virtName = String.format("reg$vtable_%d", l);
    List<String> args = new ArrayList<>();
    for(int i = 0; i < repr.getParameterCount(); i++) {
      args.add("p" + i);
    }
    args.add(0, "this");
    List<ImpExpr> fwdCalls = args.stream().map(Variable::immut).collect(Collectors.toList());

    SootClass klassSz = callees.entrySet().iterator().next().getValue().iterator().next();
    int projSize = layout.metaStorageSize(klassSz);
    InstructionStream virtBody = InstructionStream.fresh("devirt", body -> {
      List<P2<List<Integer>, InstructionStream>> actions = new ArrayList<>();

      callees.forEach((meth, kls) -> {
        List<Integer> flgs = kls.stream().map(SootClass::getNumber).collect(Collectors.toList());
        worklist.add(meth);
        String actual = getMangledName(meth);
        InstructionStream br = InstructionStream.fresh("branch", brnch -> brnch.ret(ImpExpr.call(actual, fwdCalls)));
        actions.add(P.p(flgs, br));
      });

      String runtimeTag = "ty";
      body.bindProjection(runtimeTag, 0, projSize, "this");
      List<ImpExpr> flagArg = List.of(Variable.immut(runtimeTag));

      gateLoop(body, actions.iterator(), flgs -> {
        String control = FlagTranslation.allocate(flgs);
        return ImpExpr.call(control, flagArg);
      }, i -> {
        i.addAssertFalse();
        i.ret(ImpExpr.dummyValue(repr.getReturnType()));
      });
    });
    virtBody.close();
    s.addSideFunction(virtName, args, virtBody);
    return virtName;
  }

  private interface Cleanup {
    void cleanup(InstructionStream stream);
  }

  private static abstract class LocalContents implements Cleanup {
    public abstract ImpExpr getValue();
  }

  private enum BindMode {
    INTERPROC,
    INTRAPROC
  }

  private class TempLocal extends LocalContents {
    private final String tmp;
    private final Local alias;
    public TempLocal(final String tmp, final Local local) {
      this.tmp = tmp;
      this.alias = local;
    }

    @Override public ImpExpr getValue() {
      return Variable.immut(this.tmp);
    }

    @Override public void cleanup(final InstructionStream s) {
      s.addPtrAlias(tmp, alias.getName());
    }
  }

  private class SimpleContents extends LocalContents {
    private final ImpExpr lifted;

    public SimpleContents(final ImpExpr lift) {
      this.lifted = lift;
    }

    @Override public ImpExpr getValue() {
      return lifted;
    }

    @Override public void cleanup(final InstructionStream s) {
    }
  }

  private LocalContents liftValue(Unit ctxt, Value v, VarManager m, InstructionStream s, int slot, BindMode mode, TreeMap<Local, Binding> env) {
    if(v instanceof Local) {
      Local local = (Local) v;
      if(local.getType() instanceof RefLikeType && env.get(local).some() == Binding.MUTABLE && mode == BindMode.INTERPROC) {
        String tmp = m.getBase(slot);
        s.addBinding(tmp, Variable.deref(local.getName()), false);
        return new TempLocal(tmp, local);
      }
      return new SimpleContents(lifter.lift(v, env));
    } else if(v instanceof InstanceFieldRef) {
      InstanceFieldRef fieldRef = (InstanceFieldRef) v;
      FieldPointer fp = this.unwrapField(s, fieldRef, env, m);
      return new CompoundCleanup(Variable.deref(fp.fieldName), fp);
    } else if(v instanceof ArrayRef) {
      ArrayRef ar = (ArrayRef) v;
      LocalContents c = this.unwrapArray(ar, s, env, m, slot);
      ImpExpr ind = this.lifter.lift(ar.getIndex(), env);
      return new CompoundCleanup(new ArrayRead(c.getValue(), ind), c);
    } else if(v instanceof InvokeExpr) {
      assert slot == -1;
      return this.translateCall(ctxt, s, (InvokeExpr) v, env);
    } else if(v instanceof LengthExpr) {
      LengthExpr le = (LengthExpr) v;
      LocalContents c = this.liftValue(ctxt, le.getOp(), m, s, slot, mode, env);
      return new CompoundCleanup(new ArrayLength(c.getValue()), c);
    } else {
      return new SimpleContents(lifter.lift(v, env));
    }
  }

  private LocalContents unwrapArray(final ArrayRef v, final InstructionStream s, final TreeMap<Local,Binding> env, final VarManager m, int slot) {
    Local l = (Local) v.getBase();
    if(env.get(l).some() == Binding.MUTABLE) {
      String tmp = m.getBase(slot);
      s.addBinding(tmp, Variable.deref(l.getName()), false);
      return new TempLocal(tmp, l);
    } else {
      return new SimpleContents(Variable.immut(l));
    }
  }

  private static class CompoundCleanup extends LocalContents {
    private final ImpExpr lhs;
    private final List<Cleanup> wrapped;

    public CompoundCleanup(ImpExpr lhs, Cleanup wrapped) {
      this.lhs = lhs;
      this.wrapped = List.of(wrapped);
    }

    public CompoundCleanup(ImpExpr lhs, Stream<? extends Cleanup> s) {
      this.lhs = lhs;
      this.wrapped = s.collect(Collectors.toList());
    }

    @Override public void cleanup(final InstructionStream stream) {
      this.wrapped.forEach(c -> c.cleanup(stream));
    }

    @Override public ImpExpr getValue() {
      return lhs;
    }
  }

  private static class FieldPointer implements Cleanup {
    public final String fieldName;

    private final int slot;
    private final String objectName;
    private final String storageName;

    private FieldPointer(final String fieldName, final int slot, final String objectName, final String storageName) {
      this.fieldName = fieldName;
      this.slot = slot;
      this.objectName = objectName;
      this.storageName = storageName;
    }

    public void cleanup(InstructionStream str) {
      str.addPtrProjAlias(fieldName, objectName, slot);
      if(storageName != null) {
        assert !storageName.equals(objectName);
        str.addPtrAlias(objectName, storageName);
      }
    }
  }

  private interface VarManager {
    String getBase(int i);
    String getField(int i);
  }

  private abstract class AbstractVarManager implements VarManager {
    private final String base;
    private final String field;
    private boolean readBase = false;
    private boolean readField = false;

    private BitSet bs = new BitSet();
    private BitSet fs = new BitSet();

    private final long ctxt;

    protected AbstractVarManager(Unit u, String base, String field) {
      Numberer<Unit> numberer = Scene.v().getUnitNumberer();
      numberer.add(u);
      ctxt = numberer.get(u);
      this.base = base;
      this.field = field;
    }

    @Override public String getBase(final int i) {
      validate(i, this.readBase, this.bs);
      String fmt = String.format("reg$%s_%d",base, ctxt);
      if(i == -1) {
        this.readBase = true;
        return fmt;
      } else {
        this.bs.set(i);
        return fmt + "_" + i;
      }
    }

    private void validate(final int i, final boolean flg, final BitSet set) {
      if(i < -1) {
        throw new IllegalArgumentException();
      }
      if((i == -1 && flg) || (i >= 0 && set.get(i))) {
        throw new IllegalStateException();
      }
    }

    @Override public String getField(final int i) {
      validate(i, readField, fs);
      String fmt = String.format("reg$%s_%d", this.field, ctxt);
      if(i == -1) {
        this.readField = true;
        return fmt;
      } else {
        fs.set(i);
        return fmt + "_" + i;
      }
    }
  }

  private class BindCall extends AbstractVarManager {
    public BindCall(final Unit ctxt) {
      super(ctxt, "call", null);
    }
  }

  private class LocalWrite extends AbstractVarManager {
    public LocalWrite(final Unit unit) {
      super(unit, "base", "field");
    }
  }

  private FieldPointer unwrapField(InstructionStream str, final InstanceFieldRef fieldRef, final TreeMap<Local,Binding> env, VarManager vm) {
    Local l = (Local) fieldRef.getBase();
    String fieldBase;
    String localStorage;
    if(env.get(l).some() == Binding.MUTABLE) {
      localStorage = l.getName();
      fieldBase = vm.getBase(-1);
      str.addBinding(fieldBase, Variable.deref(l.getName()), false);
    } else {
      localStorage = null;
      fieldBase = l.getName();
    }
    String fieldPtr = vm.getField(-1);
    SootField field = fieldRef.getField();
    int i = this.layout.getStorageSlot(field);
    str.bindProjection(fieldPtr, i, layout.metaStorageSize(field), fieldBase);
    return new FieldPointer(fieldPtr, i, fieldBase, localStorage);
  }

  private String getParamName(final int paramNumber) {
    return String.format("regnant$in_%s", b.getParameterLocal(paramNumber).getName());
  }

  private <R> Env encodeBasicBlock(final BasicBlock head,
      InstructionStream str,
      Function<Unit, R> extractFinal,
      final BiConsumer<Env, R> o,
      Env inEnv) {
    System.out.println("Encoding " + head);
    List<Unit> units = head.units;
    Map<Local, Binding> localStorage = alloc.letBind.getOrDefault(head, Collections.emptyMap());
    Env outEnv = inEnv.updateBound(localStorage);

    Set<Local> defInBlock = units.stream().flatMap(u ->
      u.getDefBoxes().stream().map(ValueBox::getValue).flatMap(v ->
        v instanceof Local ? Stream.of((Local)v) : Stream.empty()
      )
    ).collect(Collectors.toSet());
    Set<Local> needDefined = new HashSet<>();
    localStorage.forEach((loc, bind) -> {
      if(!defInBlock.contains(loc)) {
        assert bind == Binding.MUTABLE;
        str.addBinding(loc.getName(), ImpExpr.dummyValue(loc.getType()), true);
      } else {
        needDefined.add(loc);
      }
    });

    for(int i = 0; i < units.size() - 1; i++) {
      encodeInstruction(str, units.get(i), needDefined, outEnv.boundVars);
    }
    Unit finalUnit = units.get(units.size() - 1);
    R f = extractFinal.apply(finalUnit);
    if(f == null) {
      encodeInstruction(str, finalUnit, needDefined, outEnv.boundVars);
    }
    o.accept(outEnv, f);
    return outEnv;
  }

  private int getCoordId(Coord c) {
    return coordAssignment.computeIfAbsent(c, _c -> coordCounter++);
  }

  private class FieldOpWrite implements VarManager {
    private final String tag;
    private boolean readBase = false;
    private boolean readField = false;

    public FieldOpWrite(String tag) {
      this.tag = tag;
    }

    @Override public String getBase(final int i) {
      if(i != -1) {
        throw new IllegalArgumentException();
      }
      if(readBase) {
        throw new IllegalStateException();
      }
      readBase = true;
      return String.format("reg$%s_base", tag);
    }

    @Override public String getField(final int i) {
      if(i != -1) {
        throw new IllegalArgumentException();
      }
      if(readField) {
        throw new IllegalStateException();
      }
      readField = true;
      return String.format("reg$%s_field", tag);
    }
  }
}
