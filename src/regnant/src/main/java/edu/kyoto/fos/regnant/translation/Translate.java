package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.aliasing.FieldAliasing;
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
import edu.kyoto.fos.regnant.ir.expr.IntLiteral;
import edu.kyoto.fos.regnant.ir.expr.ValueLifter;
import edu.kyoto.fos.regnant.ir.expr.Variable;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;
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
import soot.FastHierarchy;
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
import soot.jimple.CastExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LengthExpr;
import soot.jimple.NopStmt;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.VirtualCalls;
import soot.util.NumberedString;
import soot.util.Numberer;
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
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation.*;

/*
  The big fish translation.

  A big concept is the notion of a Cleanup object. These represent the result of a simplification of some
  value form, potentially using multiple temporary variables read out of memory. After these values are used,
  the cleanup interface provides a well-defined way to indicate any temporary values are no longer needed, any may
  be aliased back as needed.


*/
public class Translate {
  private static final String THIS_PARAM = "reg$this_in";
  public static final String ALIASING_CLASS = "edu.kyoto.fos.regnant.runtime.Aliasing";
  private final FlagInstrumentation flg;
  private final Body b;
  private final LetBindAllocator alloc;
  private final InstructionStream stream;
  private final ChunkedQueue<SootMethod> worklist;
  private final StorageLayout layout;
  private final ValueLifter lifter;
  private final FieldAliasing as;
  private final ObjectModel objectModel;
  private int coordCounter = 1;
  private Map<Coord, Integer> coordAssignment = new HashMap<>();
  public static final String CONTROL_FLAG = "reg$control";

  public Translate(Body b, GraphElem startElem, FlagInstrumentation flg, LetBindAllocator alloc, final ChunkedQueue<SootMethod> worklist, StorageLayout sl, final FieldAliasing as, ObjectModel.Impl om) {
    this.flg = flg;
    this.b = b;
    this.alloc = alloc;
    this.worklist = worklist;
    this.layout = sl;
    this.objectModel = om.make(layout);
    this.lifter = new ValueLifter(worklist, layout, objectModel);
    this.as = as;
    /* the instructionstream.fresh takes a lambda which builds the instruction stream
     "in place."
     */
    this.stream = InstructionStream.fresh("main", l -> {
      // The environment does not actually track static types (we don't need it to). Rather, it tracks what the current loop name is,
      // what variables are in scope, and the binding type of each variable (i.e., wrapped in a ref type or immutable)
      Env e = Env.empty();
      // if we need to track flags during this execution, allocate the special control flag variable.
      if(flg.setFlag.size() > 0) {
        l.addBinding(CONTROL_FLAG, ImpExpr.literalInt(0), true);
        e = e.updateBound(Collections.singletonMap(new JimpleLocal(CONTROL_FLAG, IntType.v()), Binding.MUTABLE));
      }
      // translate the root start elem
      translateElem(l, startElem, e);
    });
    this.stream.close();
  }

  // print は
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
  /*
    When translating each element, we may wrap it in multiple conditionals. The first is
    a check of whether the execution of this block should occur, based on the gate on flag.
   */
  @SuppressWarnings("unchecked") private Env translateElem(InstructionStream outStream, GraphElem elem, Env e) {
    Map<String, Object> annot = elem.getAnnot();
    if(annot.containsKey(GATE_ON)) {
      Set<Coord> cond = elem.getAnnotation(GATE_ON, Set.class);
      InstructionStream i = InstructionStream.fresh("gate-top");
      translateElemChoose(i, elem, e);
      outStream.addCond(
          // this will generate a new conditional to check the value of the control flag
          ImpExpr.controlFlag(cond.stream().map(this::getCoordId).collect(Collectors.toList())),
          i.andClose(),
          InstructionStream.unit("gate"));
      return e;
    } else {
      return translateElemChoose(outStream, elem, e);
    }
  }

  /*
    The next step is to select which block to execute;
    this generates a chain of if/else expressions
   */
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

  /* i is the instruction stream on which to place the translation of the remainder of the choices */
  private void translateElemChoose(final InstructionStream i,
      final Iterator<GraphElem> iterator,
      final Map<BasicBlock,Set<Coord>> chooseBy, Env e) {
    assert iterator.hasNext();
    GraphElem hd = iterator.next();
    if(!iterator.hasNext()) {
      /*
      if this is the last possibility, directly translate onto i
       */
      translateElemLoop(i, hd, e);
    } else {
      List<Integer> choiceBy = toChoiceFlags(chooseBy.get(hd.getHead()));
      InstructionStream curr = InstructionStream.fresh("choice1");
      InstructionStream rest = InstructionStream.fresh("choice-rest");
      /*
        otherwise translate this elements body on curr
       */
      translateElemLoop(curr, hd, e);
      curr.close();
      /*
      translate the remaining elements of the stream on rest
       */
      translateElemChoose(rest, iterator, chooseBy, e);
      /* then place the conditional, decided based on the choice flag, on the stream i given to us */
      i.addCond(ImpExpr.controlFlag(choiceBy), curr, rest.andClose());
    }
  }

  private List<Integer> toChoiceFlags(final Set<Coord> tmp) {
    return tmp.stream().map(this::getCoordId).collect(Collectors.toList());
  }

  /*
    If this is a loop, lift it into a separate function, and then insert a call to that function.

    Otherwise, do the actual translation in translateElemBase
   */
  @SuppressWarnings("unchecked")
  private Env translateElemLoop(final InstructionStream i, final GraphElem elem, Env e) {
    if(elem.isLoop()) {
      Map<String, Object> annot = elem.getAnnot();
      String loopName = this.getLoopName(elem);
      List<Local> args = new ArrayList<>();
      /*
        Collect all variables in scope
       */
      e.boundVars.keys().forEach(args::add);

      InstructionStream lBody = InstructionStream.fresh("loop-body");
      /*
        Translate the loop body on the (fresh) lbody scheme
       */
      translateElemBase(lBody, elem, e.enterLoop(loopName, args));
      lBody.close();
      assert lBody.isTerminal();
      /*
        Attach the body of the function as an auxiliary function to i,
        the aux function has body lBody, name loopName, and arguments args,
       */
      i.addSideFunction(loopName, args, lBody);

      /*
        Invoke the new loop function, passing in all live arguments;
       */
      i.addLoopInvoke(loopName, args);
      List<P2<List<Integer>, InstructionStream>> doIf = new ArrayList<>();
      /*
      Add a series of conditional operations; break out of the root, or recursively invoke the current loop
       */
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
  /*
    Translate a seties of instruction streams and control flag values into a series of if/else statements.
   */
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
    return m.getDeclaringClass().getName().replace(".", "__") + "_" + m.getName().replace("<init>", "$init$");
  }

  private String getLoopName(final GraphElem elem) {
    return String.format("regnant$%s_%s__loop_%d",
        b.getMethod().getDeclaringClass().getName().replace(".", "$$"),
        b.getMethod().getName(),
        elem.getHead().id);
  }

  /*
    Compile a continuation that appears in a conditional expression. The pre consumer is for attaching cleanup operations
    generated by evaluating the condition, namely aliasing temporary variables back into their "stable" storage.
   */
  private InstructionStream compileJump(Continuation c, final Env env, Consumer<InstructionStream> pre) {
    if(c instanceof JumpCont) {
      JumpCont jumpCont = (JumpCont) c;
      Coord srcCoord = jumpCont.c;
      /*
        If we have to set a flag, return, or recurse call the jumpFrom function, otherwise do nothing
       */
      if(flg.setFlag.contains(srcCoord) || flg.returnJump.contains(srcCoord) || jumpCont.j.cont.size() > 0) {
        return InstructionStream.fresh("jump", i -> {
          pre.accept(i);
          jumpFrom(jumpCont.c, i, env);
        });
      } else {
        return InstructionStream.fresh("fallthrough", l -> {
          pre.accept(l);
          l.close();
        });
      }
    } else {
      assert c instanceof ElemCont;
      return InstructionStream.fresh("branch", l -> {
        /* the continuation is actually a block, so translate it, starting the chain against from translateElem */
        pre.accept(l);
        translateElem(l, ((ElemCont) c).elem, env);
      });
    }
  }

  private InstructionStream compileJump(Continuation c, final Env env) {
    return compileJump(c, env, i -> {});
  }

  private void jumpFrom(final Coord c, final InstructionStream i, Env e) {
    if(flg.recurseFlag.contains(c)) {
      /*
        The current loop record provides an exact name of the method and the variables available in each iteration;
        i.e., those that should be passed in as arugments
       */
      i.ret(ImpExpr.callLoop(e.currentLoop._1(), e.currentLoop._2()));
      assert !flg.setFlag.contains(c) && !flg.returnJump.contains(c);
    }
    /*
     the special i.setControl emits a mutation of the special flag variable
     */
    if(flg.setFlag.contains(c)) {
      assert !i.isTerminal();
      i.setControl(this.getCoordId(c));
    }
    // This may fire after the above, so we may set the flag and then return
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
      // we handle the translation of ifstatements ourselves.
      return encodeBasicBlock(cond.head, lBody, u -> {
        assert u instanceof IfStmt; return ((IfStmt)u);
      }, (env_, el) -> {
        Value condValue = el.getCondition();
        // based on asm source, the right (aka 2nd) op will always be null when representing ifnull/ifnonull
        // this is not terribly *robust* mind you, but serves for the moment.
        if(condValue instanceof ConditionExpr && ((ConditionExpr) condValue).getOp2().equals(NullConstant.v())) {
          ConditionExpr condE = (ConditionExpr) condValue;
          Continuation tCont, fCont;
          if(condE.getSymbol().trim().equals("==")) {
            // the TRUE branch is what we take if the pointer is null, i.e., it becomes the true branch of ifnull
            tCont = cond.tBranch;
            fCont = cond.fBranch;
          } else {
            assert condE.getSymbol().trim().equals("!=");
            // then the true branch is if we are non-null, in which case it must be swapped to be the ELSE branch
            // of our ifnull
            tCont = cond.fBranch;
            fCont = cond.tBranch;
          }
          LocalContents l = this.liftValue(el, condE.getOp1(), new FieldOpWrite("null"), lBody, BindMode.IMMEDIATE, env_.boundVars);
          lBody.addNullCond(l.getValue(), compileJump(tCont, env_, l::cleanup), compileJump(fCont, env_, l::cleanup));
        } else {
          ImpExpr path = lifter.lift(condValue, env_.boundVars);
          lBody.addCond(path, compileJump(cond.tBranch, env_).andClose(), compileJump(cond.fBranch, env_).andClose());
        }
      }, env);
    } else if(elem instanceof JumpNode) {
      JumpNode j = (JumpNode) elem;
      /*
        Override the final unit handling if it is a return statement.
       */
      return encodeBasicBlock(j.head, lBody, u -> (u instanceof ReturnStmt || u instanceof ReturnVoidStmt) ? u : null, (env_, rs_) -> {
        Coord c = Coord.of(j.head);
        /* before returning, we have to either set control flags and add parameter aliasing
          (parameters are copied into local variable names, following Soot's argument model. We need this
          aliasing to transfer the ownership back to the formal argument names
         */
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
        // otherwise this is a fall through. This will have been called after the final element has been translated, so set any flags as necessary for intra-procedural control flow
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

  // jimpleの命令を受け取って変換するメソッド
  private void encodeInstruction(final InstructionStream str, final Unit unit, // strは書き換える先、unitはjimple
      final Set<Local> needDefine,
      fj.data.TreeMap<Local, Binding> env) {
    assert !(unit instanceof IfStmt);
    assert !(unit instanceof ReturnStmt);
    if(unit instanceof NopStmt) {
      if(unit.hasTag(UnreachableTag.NAME)) {
        // despite the name, this outputs a fail statement
        str.addAssertFalse();
      }
    } else if(unit instanceof ThrowStmt) {
      throw new RuntimeException("not handled yet");
    } else if(unit instanceof IdentityStmt) {
      /*
        Bind the parameters to local storage. Parameters are immutable, so
        if the program mutates the value of a parameter local, this serves to wrap that
        value in a mkref.

        Note that mutable parameters will prevent aliasing back
       */
      IdentityStmt identityStmt = (IdentityStmt) unit;
      Value rhs = identityStmt.getRightOp();
      assert rhs instanceof IdentityRef;

      assert identityStmt.getLeftOp() instanceof Local;
      Local defn = (Local) identityStmt.getLeftOp();
      assert needDefine.contains(defn);
      assert env.contains(defn);
      needDefine.remove(defn);
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
      // the stream in which the write occurs. when possible we do this in a scope block to avoid temp variable clutter
      InstructionStream writeStream;
      if(!needsDefinition) {
        writeStream = InstructionStream.fresh("write");
      } else {
        writeStream = str;
      }
      // we allow complex RHS in binding forms
      // liftValue handles the messiness of extracting out field contents.
      LocalContents c = this.liftValue(unit, as.getRightOp(), new LocalWrite(unit), writeStream, BindMode.COMPLEX, env);
      if(needsDefinition) {
        writeStream.addBinding(target.getName(), c.getValue(), mutableBinding);
      } else {
        // target must be a reference, as any writes after the first require mutable storage
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
      this.writeField(str, fieldRef, env, right, new CtxtVarManager(unit, "base", "field"));
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof ArrayRef) {
      ArrayRef arrayRef = (ArrayRef) ((AssignStmt) unit).getLeftOp();
      InstructionStream s = InstructionStream.fresh("array");
      // the base pointer may be in mutable memory, we may need to move it into a temporary, "direct" variable.
      LocalContents basePtr = this.unwrapArray(arrayRef, s, env, new FieldOpWrite("array"));
      // By the invariants provided by soot, we know these are immediates
      ImpExpr ind = this.lifter.lift(arrayRef.getIndex(), env);
      ImpExpr val = this.lifter.lift(((AssignStmt) unit).getRightOp(), env);
      s.addArrayWrite(basePtr.getValue(), ind, val);
      basePtr.cleanup(s);
      str.addBlock(s);
    } else if(unit instanceof InvokeStmt) {
      InstructionStream call = InstructionStream.fresh("call");
      InvokeStmt is = (InvokeStmt) unit;
      // skip super object constructors
      if(is.getInvokeExpr() instanceof SpecialInvokeExpr && is.getInvokeExpr().getMethodRef().getDeclaringClass().getName().equals("java.lang.Object") && is.getInvokeExpr().getMethodRef().getName().equals("<init>")) {
        return;
      }
      // local contents here actually contains the call expression, which must be added to the stream
      // N.B>
      LocalContents c = this.translateCall(unit, call, is.getInvokeExpr(), env);
      call.addExpr(c.getValue());
      // clean up temporary values made in temporary storage as necessary
      c.cleanup(call);
      // add the block
      str.addBlock(call);
    } else if(!(unit instanceof GotoStmt)) {
      // this is really hard, do it later
      throw new RuntimeException("Unhandled statement " + unit + " " + unit.getClass());
    }
  }

  private void writeField(InstructionStream str, InstanceFieldRef fieldRef, TreeMap<Local, Binding> env, ImpExpr lhs, VarManager m) {
    /*
      We disallow writes to fields that we have aliased as must aliasing with another
     */
    if(this.as.isFinal(fieldRef.getField()) && (!this.b.getMethod().getDeclaringClass().equals(fieldRef.getField().getDeclaringClass()) || !this.b.getMethod().isConstructor())) {
      throw new UnsupportedOperationException("Must alias annotation requires field " + fieldRef.getField() + " to be effectively final");
    }
    InstructionStream i = InstructionStream.fresh("write", l -> {
      // unwrap the raw pointer representing the memory address in which the object representation is kept.
      VariableContents base = this.unwrapPointer(l, env, m, (Local) fieldRef.getBase());
      // a list of cleanups. To be processed in order
      LinkedList<Cleanup> c = new LinkedList<>();
      c.add(base);
      // the object model itself handles the translation of the field write; in so doing, it may generate more temporary variables in the block;
      // the cleanup for these variables should be added to c; they are applied in a well defined order after the write is complete.
      objectModel.writeField(l, base.getWrappedVariable(), fieldRef.getField(), lhs, m, c);
      c.forEach(h -> h.cleanup(l));
    });
    i.close();
    str.addBlock(i);
  }

  private LocalContents translateCall(Unit ctxt, InstructionStream str, InvokeExpr expr, final TreeMap<Local, Binding> env) {
    if(isRegnantIntrinsic(expr)) {
      // short circuit
      return this.handleIntrinsic(ctxt, str, env, expr);
    }
    final VarManager vm = new BindCall(ctxt);
    List<LocalContents> args = new ArrayList<>();
    String callee;
    List<Value> v = expr.getArgs();
    if(expr instanceof StaticInvokeExpr) {
      // straightforward, the method we call is the one statically named in the java bytecode.
      callee = getMangledName(expr.getMethod());
      worklist.add(expr.getMethod());
    } else if(expr instanceof SpecialInvokeExpr) {
      SootMethod m = expr.getMethod();
      worklist.add(m);
      callee = getMangledName(m);
    } else {
      assert expr instanceof InstanceInvokeExpr;
      // Points to analysis time!
      var inv = (InstanceInvokeExpr) expr;
      Local l = (Local) inv.getBase();
      PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
      NumberedString subSig = expr.getMethodRef().getSubSignature();
      // find the possible callees
      Map<SootMethod, Set<SootClass>> callees =
          pta.reachingObjects(l).possibleTypes().stream()
              .filter(RefType.class::isInstance)
              .map(RefType.class::cast)
              .collect(Collectors
                  .groupingBy(refTy -> VirtualCalls.v().resolveNonSpecial(refTy, subSig, false),
                      Collectors.mapping(RefType::getSootClass, Collectors.toSet())));
      if(callees.size() == 1) {
        // if there is just one, then this is easy, the call is direct
        SootMethod m = callees.keySet().iterator().next();
        callee = getMangledName(m);
        worklist.add(m);
      } else {
        // de-virtualize. The result of this operation will be a function with exactly the interface of the expected callee
        callee = devirtualize(ctxt, str, callees);
      }
    }
    // Lift all of the arguments to immediate values with cleanups, as represented by LocalContents
    if(expr instanceof InstanceInvokeExpr) {
      InstanceInvokeExpr iie = (InstanceInvokeExpr) expr;
      args.add(liftValue(ctxt, iie.getBase(), vm, str, BindMode.IMMEDIATE, env));
    }
    for(Value a : v) {
      var lifted = liftValue(ctxt, a, vm, str, BindMode.IMMEDIATE, env);
      args.add(lifted);
    }
    // Generate the call itself, using the immediate forms generated above
    ImpExpr call = ImpExpr.call(callee, args.stream().map(LocalContents::getValue).collect(Collectors.toList()));
    // this translated call, and the cleanups of each argument form the cleanup-annotated value of the call
    return new CompoundCleanup(call, args.stream());
  }

  private LocalContents handleIntrinsic(Unit ctxt, final InstructionStream str, TreeMap<Local, Binding> env, final InvokeExpr expr) {
    if(expr.getMethodRef().getName().equals("rand")) {
      assert expr.getMethodRef().getDeclaringClass().getName().equals(RandomRewriter.RANDOM_CLASS);
      return new SimpleContents(ImpExpr.nondet());
    } else if(expr.getMethodRef().getName().equals("noAutoReturn")) {
      // ignored
      return new SimpleContents(ImpExpr.unitValue());
    } else {
      assert expr.getMethodRef().getDeclaringClass().getName().equals(ALIASING_CLASS);
      assert expr.getMethodRef().getName().equals("alias");
      VarManager vm = new CtxtVarManager(ctxt, "alias", "fld");
      if(expr.getArgCount() == 3) {
        assert expr.getMethodRef().getSubSignature().getString().equals("void alias(java.lang.Object,java.lang.Object,java.lang.String)") : expr.getMethodRef().getSubSignature();
        /*
        Extract the two object variables and the field name. This is for asserting that x = y.f must alias, expressed as
        alias(x, y, "f") (the f string is quite kludgy)
         */
        Value fldName = expr.getArg(2);
        if(!(fldName instanceof StringConstant)) {
          throw new RuntimeException("Non-constant field name in alias expression");
        }
        String name = ((StringConstant) fldName).value;
        Value op1 = expr.getArg(0);
        Value op2 = expr.getArg(1);
        if(!(op1 instanceof Local) || !(op2 instanceof Local)) {
          throw new RuntimeException("Alias arguments must be plain local variables");
        }
        Type r = op2.getType();
        assert r instanceof RefType;
        var kls = ((RefType) r).getSootClass();
        SootField sf = getDeclaredField(kls, name);
        if(sf == null) {
          throw new RuntimeException("No field " + name + " declared in the type hierarchy of " + kls);
        }
        if(!(sf.getType() instanceof RefLikeType)) {
          throw new RuntimeException("Field " + name + " must be a reference field");
        }
        Local r1 = (Local) op1;
        Local r2 = (Local) op2;

        /* this returns an access path builder rooted at the given local variable.
          It automatically handles the insertion of a dereference
         */
        Function<Local, Builder> builderRoot = l -> {
          Builder b = AliasOp.buildAt(l.getName());
          if(env.get(l).some() == Binding.MUTABLE) {
            b.deref();
          }
          return b;
        };

        AliasOp p1 = builderRoot.apply(r1).build();
        AliasOp p2 = objectModel.extendAP(builderRoot.apply(r2), sf).build();

        // BUT BEFORE ALL THIS, we must return the auto aliases, (if any)
        /* If we are aliasing with a field where another other object reachable from the base pointer
           aliases with this fields contents, we have to automatically alias with that object as well


           XXX(jtoman): is this right...?
         */
        var autoAliasing = as.getAutoAliasing(sf);
        if(!this.b.getMethod().isConstructor()) {
          autoAliasing.forEach(l -> {
            AliasOp a1 = builderRoot.apply(r1).iter(l._1().stream(), objectModel::iterAP).build();
            AliasOp a2 = builderRoot.apply(r2).iter(l._2().stream(), objectModel::iterAP).build();
            str.addAlias(a1, a2);
          });
        }
        str.addAlias(p1, p2);
        return new SimpleContents(ImpExpr.unitValue());
      } else {
        assert expr.getArgCount() == 2;
        Value op1 = expr.getArg(0);
        Value op2 = expr.getArg(1);
        if(!(op1 instanceof Local) || !(op2 instanceof Local)) {
          throw new RuntimeException("Alias argument must be plain local variables");
        }
        VariableContents c1 = this.unwrapPointer(str, env, vm, (Local) op1);
        VariableContents c2 = this.unwrapPointer(str, env, vm, (Local) op2);
        str.addAlias(c1.getWrappedVariable(), c2.getWrappedVariable());
        return new CompoundCleanup(ImpExpr.unitValue(), Stream.of(c1, c2));
      }
    }
  }

  private static SootField getDeclaredField(SootClass klass, String fldName) {
    while(true) {
      if(klass.declaresFieldByName(fldName)) {
        return klass.getFieldByName(fldName);
      }
      if(klass.hasSuperclass()) {
        klass = klass.getSuperclass();
      } else {
        return null;
      }
    }
  }

  private boolean isRegnantIntrinsic(final InvokeExpr expr) {
    return expr instanceof StaticInvokeExpr &&
        ((expr.getMethodRef().getDeclaringClass().getName().equals(RandomRewriter.RANDOM_CLASS) && expr.getMethodRef().getName().equals("rand")) ||
            expr.getMethodRef().getDeclaringClass().getName().equals(ALIASING_CLASS));
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
    // generate pass through parameters
    for(int i = 0; i < repr.getParameterCount(); i++) {
      args.add("p" + i);
    }
    args.add(0, "this");
    // these are the arguments we will be directly forwarding to the devirtualized targets
    List<ImpExpr> fwdCalls = args.stream().map(Variable::immut).collect(Collectors.toList());

    /* this is a gross hack to get the size of the tuple used to store objects of the static type of the receiver */
    SootClass klassSz = callees.entrySet().iterator().next().getValue().iterator().next();
    int projSize = layout.metaStorageSize(klassSz);
    InstructionStream virtBody = InstructionStream.fresh("devirt", body -> {
      List<P2<List<Integer>, InstructionStream>> actions = new ArrayList<>();
      /*
        This is a list of the possible instruction streams that call the target method, and the runtime tags that resolve to that method.
       */
      callees.forEach((meth, kls) -> {
        List<Integer> flgs = kls.stream().map(SootClass::getNumber).collect(Collectors.toList());
        worklist.add(meth);
        String actual = getMangledName(meth);
        InstructionStream br = InstructionStream.fresh("branch", brnch -> brnch.ret(ImpExpr.call(actual, fwdCalls)));
        actions.add(P.p(flgs, br));
      });

      String runtimeTag = "ty";
      // project the runtime tag out
      body.bindProjection(runtimeTag, 0, projSize, "this");
      List<ImpExpr> flagArg = List.of(Variable.immut(runtimeTag));
      // use the same machinery as the recurse-on/return-on flags to generate the if/else flags, but the final else block must be a fail (devirtualization shouldn't fail)
      gateLoop(body, actions.iterator(), flgs -> {
        String control = FlagTranslation.allocate(flgs);
        return ImpExpr.call(control, flagArg);
      }, InstructionStream::addAssertFalse);
    });
    virtBody.close();
    s.addSideFunction(virtName, args, virtBody);
    return virtName;
  }

  private static abstract class LocalContents implements Cleanup {
    public abstract ImpExpr getValue();
  }

  /*
    Variable contents is a local contents (aka, local value) that must be a variable.
    It may or may not have clean up actions
   */
  private static abstract class VariableContents extends LocalContents {
    public abstract String getWrappedVariable();
  }

  /*
    When lifting a value, how complete should the lifting be. e.g., if we need access to the value of a variable, is *x sufficient (assuming x is a mutable variable)
    or do we need t where t is bound by let t = *x in ...
   */
  private enum BindMode {
    IMMEDIATE, COMPLEX
  }

  /*
    a temp local represents the value of a mutable variable, unwrapped from the mutable reference and stored in tmp. alias is the name of the (reference typed) variable
    into which tmp should be returned when done.
   */
  private static class TempLocal extends VariableContents {
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

    @Override public String getWrappedVariable() {
      return tmp;
    }
  }

  /*
    Nothing, no temporary variables or aliasing required
   */
  private static class SimpleContents extends LocalContents {
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

  private LocalContents liftValue(Unit ctxt, Value v, VarManager m, InstructionStream s, BindMode mode, TreeMap<Local, Binding> env) {
    if(v instanceof Local) {
      Local local = (Local) v;
      if(local.getType() instanceof RefLikeType && env.get(local).some() == Binding.MUTABLE && mode == BindMode.IMMEDIATE) {
        String tmp = m.getBase();
        s.addBinding(tmp, Variable.deref(local.getName()), false);
        return new TempLocal(tmp, local);
      }
      return new SimpleContents(lifter.lift(v, env));
    } else if(v instanceof InstanceFieldRef) {
      InstanceFieldRef fieldRef = (InstanceFieldRef) v;
      VariableContents base = this.unwrapPointer(s, env, m, (Local) fieldRef.getBase());
      LinkedList<Cleanup> handlers = new LinkedList<>();
      /*
        Check if we have an assignment like x = x.f. If so, we should NOT try to alias back the
        the base contents of x, it will NOT alias anymore.
       */
      if(ctxt.getDefBoxes().stream().map(ValueBox::getValue).noneMatch(fieldRef.getBase()::equals)) {
        handlers.push(base);
      }
      FieldContents fc = this.objectModel.readField(s, base.getWrappedVariable(), fieldRef.getField(), m, handlers);

      SootField f = fieldRef.getField();
      var autoAlias = as.getAutoAliasing(f);
      // if we read this field, we must have that another object reachable from the same base pointer must alias with the object we just read.
      // automatically generate an aliasing assertion between that object and the value just read
      if(!autoAlias.isEmpty() && !this.b.getMethod().isConstructor()) {
        for(var fseq : autoAlias) {
          List<SootField> resSubFields = fseq._1();
          List<SootField> srcSubField = fseq._2();
          AliasOp op1 = fc.ap().iter(resSubFields.stream(), (sf,b) -> objectModel.extendAP(b, sf)).build();
          AliasOp op2 = AliasOp.buildAt(base.getWrappedVariable()).iter(srcSubField.stream(), (sf,b) -> objectModel.extendAP(b, sf)).build();
          s.addAlias(op1, op2);
        }
      }
      return new CompoundCleanup(fc.getExpr(), handlers.stream());
    } else if(v instanceof ArrayRef) {
      ArrayRef ar = (ArrayRef) v;
      LocalContents c = this.unwrapArray(ar, s, env, m);
      ImpExpr ind = this.lifter.lift(ar.getIndex(), env);
      return new CompoundCleanup(new ArrayRead(c.getValue(), ind), c);
    } else if(v instanceof InvokeExpr) {
      return this.translateCall(ctxt, s, (InvokeExpr) v, env);
    } else if(v instanceof LengthExpr) {
      LengthExpr le = (LengthExpr) v;
      LocalContents c = this.liftValue(ctxt, le.getOp(), m, s, mode, env);
      return new CompoundCleanup(new ArrayLength(c.getValue()), c);
    } else if(v instanceof CastExpr) {
      /* a cast is translated into a check of the runtime tags, to see if all tags are consistent with the static type given in the cast
        If so, then nothing happens (the static type in ConSORT remains the same). If not, the cast fails, and thus the program goes to the fail configuration

        (Note we could catch castclassexceptions, but no one ever does...?)
       */
      CastExpr ce = (CastExpr) v;
      Value op = ce.getOp();
      Local castOp = (Local) op;
      VariableContents l = this.unwrapPointer(s, env, m, castOp);
      String runtimeTag = m.getField();
      assert op.getType() instanceof RefType;
      PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
      Set<Type> opTypes = pta.reachingObjects(castOp).possibleTypes();
      SootClass repr = getRepresentativeClass(opTypes);
      int sz = layout.metaStorageSize(repr);
      s.bindProjection(runtimeTag, 0, sz, l.getWrappedVariable());
      Type ty = ce.getCastType();
      assert ty instanceof RefType;
      FastHierarchy fh = Scene.v().getOrMakeFastHierarchy();
      // XXX(jtoman): this could be better computed with points-to info
      // What runtime tags are valid choices for this static type
      List<Integer> validDownCasts = opTypes.stream().filter(reachTy -> fh.canStoreType(reachTy, ty) && reachTy instanceof RefType).map(RefType.class::cast)
          .map(RefType::getSootClass).map(SootClass::getNumber).collect(Collectors.toList());
      if(validDownCasts.size() == 0) {
        System.out.println("Apparently impossible cast???");
        s.addAssertFalse();
        return new SimpleContents(edu.kyoto.fos.regnant.ir.expr.NullConstant.v());
      }
      String test = FlagTranslation.allocate(validDownCasts);
      ImpExpr checkCall = ImpExpr.call(test, List.of(Variable.immut(runtimeTag)));
      s.addCond(checkCall, InstructionStream.fresh("valid-cast", InstructionStream::close), InstructionStream.fresh("invalid-cast", InstructionStream::addAssertFalse));
      return l;
    } else if(v instanceof InstanceOfExpr) {
      // TODO(jtoman): handle impossible casts
      InstanceOfExpr instExpr = (InstanceOfExpr) v;
      assert instExpr.getOp() instanceof Local;
      Local check = (Local) instExpr.getOp();
      PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
      Type checkType = instExpr.getCheckType();
      FastHierarchy fh = Scene.v().getOrMakeFastHierarchy();
      Set<Type> opTypes = pta.reachingObjects(check).possibleTypes();
      // as above, what are the possible runtime tags that are instances of the interrogated type
      List<Integer> collect = opTypes.stream()
          .filter(ty -> fh.canStoreType(ty, checkType))
          .filter(RefType.class::isInstance)
          .map(r -> ((RefType) r).getSootClass())
          .map(SootClass::getNumber)
          .distinct()
          .collect(Collectors.toList());
      VariableContents c = this.unwrapPointer(s, env, m, check);
      // get a temporary variable to store the contents of this check, it has to proceed is several steps
      String tmp = m.getBase();
      s.addBinding(tmp, ImpExpr.literalInt(0), true);
      // if the value is null, then it is definitely not an instance
      InstructionStream isNull = InstructionStream.fresh("is-null-branch", l -> l.addWrite(tmp, IntLiteral.v(0)));
      // if it is not null, then interrogate the runtime tag.
      InstructionStream isInhabited = InstructionStream.fresh("non-null-branch", l -> {
        int sz = layout.metaStorageSize(getRepresentativeClass(opTypes));
        String runtimeField = m.getField();
        l.bindProjection(runtimeField, 0, sz, c.getWrappedVariable());
        // generate a check that queries if the runtime tag is one of the possible tags
        String isSubPred = FlagTranslation.allocate(collect, true);
        ImpExpr checkCall = ImpExpr.call(isSubPred, Variable.immut(runtimeField));
        l.addWrite(tmp, checkCall);
      });
      // wrap the two possibilities into a conditional
      s.addNullCond(c.getValue(), isNull, isInhabited);
      return new CompoundCleanup(Variable.deref(tmp), c);
    } else {
      return new SimpleContents(lifter.lift(v, env));
    }
  }

  private SootClass getRepresentativeClass(final Set<Type> opTypes) {
    assert layout.haveSameRepr(opTypes.stream().map(t -> ((RefType) t).getSootClass()));
    return ((RefType) opTypes.iterator().next()).getSootClass();
  }

  private LocalContents unwrapArray(final ArrayRef v, final InstructionStream s, final TreeMap<Local, Binding> env, final VarManager m) {
    Local l = (Local) v.getBase();
    return unwrapPointer(s, env, m, l);
  }

  private VariableContents unwrapPointer(final InstructionStream s, final TreeMap<Local, Binding> env, final VarManager m, final Local l) {
    // Get the raw address (or null) of the pointer in a single variable name. This may require a dereference.
    if(env.get(l).some() == Binding.MUTABLE) {
      String tmp = m.getBase();
      s.addBinding(tmp, Variable.deref(l.getName()), false);
      return new TempLocal(tmp, l);
    } else {
      return new VariableContents() {
        @Override public String getWrappedVariable() {
          return l.getName();
        }

        @Override public ImpExpr getValue() {
          return Variable.immut(l);
        }

        @Override public void cleanup(final InstructionStream stream) {

        }
      };
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

  private static class CtxtVarManager implements VarManager {
    private final String base;
    private final String field;

    private final long ctxt;

    protected CtxtVarManager(Unit u, String base, String field) {
      Numberer<Unit> numberer = Scene.v().getUnitNumberer();
      numberer.add(u);
      ctxt = numberer.get(u);
      this.base = base;
      this.field = field;
    }

    private int baseCounter = 0;
    private int fieldCounter = 0;

    @Override public String getBase() {
      String fmt = String.format("reg$%s_%d",base, ctxt);
      int st = baseCounter++;
      if(st == 0) {
        return fmt;
      } else {
        return fmt + "_" + st;
      }
    }

    @Override public String getField() {
      String fmt = String.format("reg$%s_%d", this.field, ctxt);
      int st = fieldCounter++;
      if(st == 0) {
        return fmt;
      } else {
        return fmt + "_" + st;
      }
    }
  }

  private static class BindCall extends CtxtVarManager {
    public BindCall(final Unit ctxt) {
      super(ctxt, "call", null);
    }
  }

  private static class LocalWrite extends CtxtVarManager {
    public LocalWrite(final Unit unit) {
      super(unit, "base", "field");
    }
  }

  private String getParamName(final int paramNumber) {
    return String.format("regnant$in_%s", b.getParameterLocal(paramNumber).getName());
  }

  /*
    Encodes a basic block into the stream str. In come cases, the final element of the stream may need special handling or must be skipped.
    This is done with the extractFinal and o argument. If the extract final returns null, then it indicates it wants
    the final unit to be translated. In either event, value extracted with extractFinal is then passed to o
   */
  // 命令の基本ブロックを次々受け取ってencodeInstructionに渡している
  private <R> Env encodeBasicBlock(final BasicBlock head,
      InstructionStream str,
      Function<Unit, R> extractFinal,
      final BiConsumer<Env, R> o,
      Env inEnv) {
    // System.out.println("Encoding " + head);
    List<Unit> units = head.units;
    /*
      These are the variables that need to be bound in this block.
     */
    Map<Local, Binding> localStorage = alloc.letBind.getOrDefault(head, Collections.emptyMap());
    Env outEnv = inEnv.updateBound(localStorage);

    /* These variables are actually defined with an assignment within the block, so their assignment may be deferred. Variables
      whose assignment do not appear in the block occur when a variable is only assigned in two branches of a conditional; for the scoping to work
      out in IMPerial, we need to have the variable declared in the common ancester block of the two branches.
     */
    Set<Local> defInBlock = units.stream().flatMap(u ->
      u.getDefBoxes().stream().map(ValueBox::getValue).flatMap(v ->
        v instanceof Local ? Stream.of((Local)v) : Stream.empty()
      )
    ).collect(Collectors.toSet());
    Set<Local> needDefined = new HashSet<>();
    localStorage.forEach((loc, bind) -> {
      if(!defInBlock.contains(loc)) {
        /* Those variables that require this ahead of time declaration are given dummy values, bound before translating the rest of the block.
          These variables must be mutable, otherwise there is no feasible way to declare them ahead of time, and indeed, there is no need to
         */
        assert bind == Binding.MUTABLE;
        str.addBinding(loc.getName(), ImpExpr.dummyValue(loc.getType()), true);
      } else {
        // need defined tracks which variables declared in this block still require definition. Essentially the first write to
        // a variable will create a let binding, but all future bindings translate to assignments
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

  private static class FieldOpWrite implements VarManager {
    private final String tag;
    private boolean readBase = false;
    private boolean readField = false;

    public FieldOpWrite(String tag) {
      this.tag = tag;
    }

    @Override public String getBase() {
      if(readBase) {
        throw new IllegalStateException();
      }
      readBase = true;
      return String.format("reg$%s_base", tag);
    }

    @Override public String getField() {
      if(readField) {
        throw new IllegalStateException();
      }
      readField = true;
      return String.format("reg$%s_field", tag);
    }
  }
}
