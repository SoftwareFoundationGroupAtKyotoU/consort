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
import edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation;
import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.storage.LetBindAllocator;
import fj.Ord;
import fj.P;
import fj.P2;
import fj.data.TreeMap;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.NopStmt;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.jimple.internal.JimpleLocal;
import soot.util.queue.ChunkedQueue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation.*;

public class Translate {
  private final FlagInstrumentation flg;
  private final Body b;
  private final LetBindAllocator alloc;
  private final InstructionStream stream;
  private final ChunkedQueue<SootMethod> worklist;
  private int coordCounter = 1;
  private Map<Coord, Integer> coordAssignment = new HashMap<>();
  public static final String CONTROL_FLAG = "_reg_control";

  public Translate(Body b, GraphElem startElem, FlagInstrumentation flg, LetBindAllocator alloc, final ChunkedQueue<SootMethod> worklist) {
    this.flg = flg;
    this.b = b;
    this.alloc = alloc;
    this.worklist = worklist;
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
      List<String> argNames = p._2().stream().map(Local::getName).collect(Collectors.toList());
      sb.append(p._3().dumpAs(p._1(), argNames));
    });
    List<String> params = new ArrayList<>();
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

      String tmpName = loopName + "_ret";
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
    P2<List<Integer>, InstructionStream> g = instStream.next();
    final InstructionStream elseBranch;
    if(instStream.hasNext()) {
      elseBranch = InstructionStream.fresh("gate-choice", l -> gateLoop(l, instStream));
    } else {
      elseBranch = InstructionStream.unit("fallthrough");
    }
    tgt.addCond(ImpExpr.controlFlag(g._1()), g._2(), elseBranch);
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
        return InstructionStream.fresh("jump", i -> {
          jumpFrom(jumpCont.c, i, env);
        });
      } else {
        return InstructionStream.unit("fallthrough");
      }
    } else {
      assert c instanceof ElemCont;
      return InstructionStream.fresh("branch", l -> {
        translateElem(l, ((ElemCont) c).elem, env);
      });
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
        ImpExpr path = ImpExpr.liftCond(el.getCondition(), env_.boundVars, this.worklist);
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
          lBody.ret(ImpExpr.liftValue(rs.getOp(), env_.boundVars, this.worklist));
          return;
        } else if(rs_ instanceof ReturnVoidStmt) {
          if(flg.setFlag.contains(c)) {
            lBody.setControl(this.getCoordId(c));
          }
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
    }
    return env;
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
      // hahaha oo later
      if(rhs instanceof ThisRef) {
        return;
      }
      assert rhs instanceof ParameterRef;
      int paramNumber = ((ParameterRef) rhs).getIndex();
      assert identityStmt.getLeftOp() instanceof Local;
      Local defn = (Local) identityStmt.getLeftOp();
      assert needDefine.contains(defn);
      assert env.contains(defn);

      needDefine.remove(defn);
      str.addBinding(defn.getName(), ImpExpr.var(this.getParamName(paramNumber)), env.get(defn).some() == Binding.MUTABLE);
    } else if(unit instanceof AssignStmt) {
      AssignStmt as = (AssignStmt) unit;
      Value lhs = as.getLeftOp();
      // fields and arrays lataaaa
      assert lhs instanceof Local;
      Local target = (Local) lhs;
      if(needDefine.contains(target)) {
        str.addBinding(target.getName(), ImpExpr.liftValue(as.getRightOp(), env, this.worklist), env.get(target).some() == Binding.MUTABLE);
      } else {
        assert env.get(target).some() == Binding.MUTABLE;
        str.addWrite(target.getName(), ImpExpr.liftValue(as.getRightOp(), env, this.worklist));
      }
    } else if(unit instanceof InvokeStmt && ((InvokeStmt) unit).getInvokeExpr() instanceof StaticInvokeExpr) {
      StaticInvokeExpr staticInv = (StaticInvokeExpr) ((InvokeStmt) unit).getInvokeExpr();
      // I think soot resolves this for us
      SootMethod callee = staticInv.getMethod();
      this.worklist.add(callee);
      List<Value> args = staticInv.getArgs();
      String nm = getMangledName(callee);
      List<ImpExpr> arguments = args.stream().map(v -> ImpExpr.liftValue(v, env, this.worklist)).collect(Collectors.toList());
      str.addInvoke(nm, arguments);
    } else if(!(unit instanceof GotoStmt)) {
      // this is really hard, do it later
      throw new RuntimeException("Unhandled statement " + unit + " " + unit.getClass());
    }
  }

  private String getParamName(final int paramNumber) {
    return String.format("_regnantIn_%s", b.getParameterLocal(paramNumber).getName());
  }

  private <R> Env encodeBasicBlock(final BasicBlock head,
      InstructionStream str,
      Function<Unit, R> extractFinal,
      final BiConsumer<Env, R> o,
      Env inEnv) {
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
}