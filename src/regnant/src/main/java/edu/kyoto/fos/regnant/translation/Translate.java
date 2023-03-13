package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.aliasing.FieldAliasing;
import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.cfg.BasicBlockGraph;
import edu.kyoto.fos.regnant.cfg.BasicBlockMapper;
import edu.kyoto.fos.regnant.cfg.graph.Coord;
import edu.kyoto.fos.regnant.ir.expr.NullConstant;
import edu.kyoto.fos.regnant.ir.expr.*;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;
import edu.kyoto.fos.regnant.simpl.RandomRewriter;
import edu.kyoto.fos.regnant.storage.Binding;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import fj.Ord;
import fj.P;
import fj.P2;
import fj.data.Option;
import fj.data.TreeMap;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.VirtualCalls;
import soot.util.NumberedString;
import soot.util.Numberer;
import soot.util.queue.ChunkedQueue;

import java.io.IOException;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kyoto.fos.regnant.translation.InstructionStream.fresh;

/*
  The big fish translation.

  A big concept is the notion of a Cleanup object. These represent the result of a simplification of some
  value form, potentially using multiple temporary variables read out of memory. After these values are used,
  the cleanup interface provides a well-defined way to indicate any temporary values are no longer needed, any may
  be aliased back as needed.


*/
public class Translate {
  public static final String THIS_PARAM = "reg$this_in";
  public static final String ALIASING_CLASS = "edu.kyoto.fos.regnant.runtime.Aliasing";
  private final Body b;
  private final InstructionStream stream;
  private final ChunkedQueue<SootMethod> worklist;
  private final StorageLayout layout;
  private final ValueLifter lifter;
  private final FieldAliasing as;
  private final ObjectModel objectModel;
  private int coordCounter = 1;
  private final Map<Coord, Integer> coordAssignment = new HashMap<>();
  public static final String CONTROL_FLAG = "reg$control";
  private final BasicBlockMapper bbm;
  private final BasicBlockGraph bbg;

  public Translate(Body b, final ChunkedQueue<SootMethod> worklist, StorageLayout sl, final FieldAliasing as, ObjectModel.Impl om, BasicBlockMapper bbm, BasicBlockGraph bbg) {
    this.b = b;
    this.worklist = worklist;
    this.layout = sl;
    this.objectModel = om.make(layout);
    this.lifter = new ValueLifter(worklist, layout, objectModel);
    this.as = as;
    this.bbm = bbm;
    this.bbg = bbg;

    // TODO: envは各変数がmutableかどうかを表すMap。これをデータフロー解析で作れるようにする
    Env empty = Env.empty();
    Map<Local, Binding> binding = new HashMap<>();
    for (Local l: b.getLocals()) {
      binding.put(l, Binding.MUTABLE);
    }
    Env env = empty.updateBound(binding);

    /* the instructionstream.fresh takes a lambda which builds the instruction stream
     "in place."
     */
    this.stream = fresh("main", is -> translateMethod(is, env));
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


  // The class in which the type of each variable and whether it can be changed is maintained
  protected static class Env {
    final fj.data.TreeMap<Local, Binding> boundVars;

    Env(final TreeMap<Local, Binding> boundVars) {
      this.boundVars = boundVars;
    }

    public Env updateBound(Map<Local, Binding> b) {
      TreeMap<Local, Binding> newBind = fj.data.Stream.iterableStream(b.entrySet()).foldLeft((curr, elem) ->
          curr.set(elem.getKey(), elem.getValue()), boundVars);
      return new Env(newBind);
    }

    private static Env empty() {
      return new Env(fj.data.TreeMap.empty(Ord.ord(l1 -> l2 -> Ord.intOrd.compare(l1.getNumber(), l2.getNumber()))));
    }
  }

  private String getMangledName() {
    SootMethod m = this.b.getMethod();
    return getMangledName(m);
  }

  public static String getMangledName(final SootMethod m) {
    return m.getDeclaringClass().getName().replace(".", "__") + "_" + m.getName().replace("<init>", "$init$");
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

  private void encodeInstruction(final InstructionStream is, final Unit unit, TreeMap<Local, Binding> env, BasicBlock bb) {
    if(unit instanceof IfStmt) {
      IfStmt ifUnit = (IfStmt) unit;
      List<BasicBlock> nextBBs = bbg.getSuccsOf(bb);

      assert (nextBBs.size() == 2);
      BasicBlock thenBB;
      BasicBlock elseBB;
      // Conditional branches are converted to jumps between basic blocks
      if (ifUnit.getTarget() == nextBBs.get(0).getHead()) {
        thenBB = nextBBs.get(0);
        elseBB = nextBBs.get(1);
      } else {
        thenBB = nextBBs.get(1);
        elseBB = nextBBs.get(0);
      }
      is.addCond(lifter.lift(ifUnit.getCondition(), env), thenBB, elseBB, b, getMangledName());
    } else if(unit instanceof ReturnStmt) {
      ReturnStmt returnUnit = (ReturnStmt) unit;
      is.addReturn(lifter.lift(returnUnit.getOp(), env));
    } else if(unit instanceof ReturnVoidStmt) {
      is.addReturn(new IntLiteral(0));
    } else if(unit instanceof GotoStmt) {
      List<BasicBlock> nextBBs = bbg.getSuccsOf(bb);
      assert (nextBBs.size() == 1);
      BasicBlock nextBB = nextBBs.get(0);

      // Converts a goto statement to a function call because it corresponds to a jump between basic blocks
      is.addExpr(new InterBasicBlockCall(b, nextBB, getMangledName()));
    } else if(unit instanceof NopStmt) {
      if(unit.hasTag(UnreachableTag.NAME)) {
        // despite the name, this outputs a fail statement
        is.addAssertFalse();
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

      // TODO: 基本ブロックの一番初めのみfalseになるようにすれば良いと思う（多分）
      boolean mutableParam = true;

      if(rhs instanceof ThisRef) {
        // TODO: データフロー解析に対応したら、一旦はじめに全ての変数を定義することがなくなるため、おそらくaddBindingになる
        // is.addBinding(defn.getName(), ImpExpr.var(THIS_PARAM), mutableParam);
        is.addWrite(defn.getName(), ImpExpr.var(THIS_PARAM));
      } else {
        assert rhs instanceof ParameterRef;
        int paramNumber = ((ParameterRef) rhs).getIndex();
        // TODO: データフロー解析に対応したら、一旦はじめに全ての変数を定義することがなくなるため、おそらくaddBindingになる
        // is.addBinding(defn.getName(), ImpExpr.var(this.getParamName(paramNumber)), mutableParam);
        is.addWrite(defn.getName(), ImpExpr.var(this.getParamName(paramNumber)));
      }
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof Local) {
      AssignStmt as = (AssignStmt) unit;
      Value lhs = as.getLeftOp();
      Local target = (Local) lhs;

      // TODO: データフロー解析で判定できるよにする
      boolean needsDefinition = false;
      boolean mutableBinding = env.get(target).some() == Binding.MUTABLE;

      // the stream in which the write occurs. when possible we do this in a scope block to avoid temp variable clutter
      InstructionStream writeStream;
      if(!needsDefinition) {
        writeStream = fresh("write");
      } else {
        writeStream = is;
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
        is.addBlock(writeStream);
      }
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof InstanceFieldRef) {
      AssignStmt assign = (AssignStmt) unit;
      // TODO: その変数がmutableかどうかをデータフロー解析で行う
      ImpExpr right = lifter.lift(assign.getRightOp(), env);
      InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getLeftOp();
      this.writeField(is, fieldRef, env, right, new CtxtVarManager(unit, "base", "field"));
    } else if(unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp() instanceof ArrayRef) {
      ArrayRef arrayRef = (ArrayRef) ((AssignStmt) unit).getLeftOp();
      InstructionStream s = fresh("array");
      // the base pointer may be in mutable memory, we may need to move it into a temporary, "direct" variable.
      LocalContents basePtr = this.unwrapArray(arrayRef, s, env, new FieldOpWrite("array"));
      // By the invariants provided by soot, we know these are immediates
      ImpExpr ind = this.lifter.lift(arrayRef.getIndex(), env);
      ImpExpr val = this.lifter.lift(((AssignStmt) unit).getRightOp(), env);
      s.addArrayWrite(basePtr.getValue(), ind, val);
      basePtr.cleanup(s);
      is.addBlock(s);
    } else if(unit instanceof InvokeStmt) {
      InstructionStream call = fresh("call");
      InvokeStmt iStmt = (InvokeStmt) unit;
      // skip super object constructors
      if(iStmt.getInvokeExpr() instanceof SpecialInvokeExpr && iStmt.getInvokeExpr().getMethodRef().getDeclaringClass().getName().equals("java.lang.Object") && iStmt.getInvokeExpr().getMethodRef().getName().equals("<init>")) {
        return;
      }
      // local contents here actually contains the call expression, which must be added to the stream
      // N.B>
      LocalContents c = this.translateCall(unit, call, iStmt.getInvokeExpr(), env);
      call.addExpr(c.getValue());
      // clean up temporary values made in temporary storage as necessary
      c.cleanup(call);
      // add the block
      is.addBlock(call);
    } else {
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
    InstructionStream i = fresh("write", l -> {
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
    // Lift all the arguments to immediate values with cleanups, as represented by LocalContents
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

  // the function to branch a method to be called by the class
  private void gateLoop(final InstructionStream tgt,
                        final Iterator<P2<Integer,InstructionStream>> instStream,
                        final Function<Integer,ImpExpr> cond,
                        final Consumer<InstructionStream> fallThrough) {
    P2<Integer, InstructionStream> g = instStream.next();
    final InstructionStream elseBranch;
    if(instStream.hasNext()) {
      elseBranch = InstructionStream.fresh("gate-choice", l -> gateLoop(l, instStream, cond, fallThrough));
      elseBranch.close();
    } else {
      elseBranch = InstructionStream.fresh("fallthrough", fallThrough);
    }
    tgt.addCond(cond.apply(g._1()), g._2(), elseBranch);
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
    InstructionStream virtBody = fresh("devirt", body -> {
      List<P2<Integer, InstructionStream>> actions = new ArrayList<>();
      /*
        This is a list of the possible instruction streams that call the target method, and the runtime tags that resolve to that method.
       */
      callees.forEach((meth, kls) -> {
        List<Integer> flgs = kls.stream().map(SootClass::getNumber).collect(Collectors.toList());
        worklist.add(meth);
        String actual = getMangledName(meth);
        InstructionStream br = fresh("branch", brnch -> brnch.ret(ImpExpr.call(actual, fwdCalls)));

        for(Integer flg : flgs) {
          actions.add(P.p(flg, br));
        }
      });

      String runtimeTag = "ty";
      // project the runtime tag out
      body.bindProjection(runtimeTag, 0, projSize, "this");
      // use the same machinery as the recurse-on/return-on flags to generate the if/else flags, but the final else block must be a fail (devirtualization shouldn't fail)
      gateLoop(body, actions.iterator(), flg -> new Binop(new Variable(runtimeTag, false), "=", new IntLiteral(flg)), InstructionStream::addAssertFalse);
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
      s.addCond(checkCall, fresh("valid-cast", InstructionStream::close), fresh("invalid-cast", InstructionStream::addAssertFalse));
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
      InstructionStream isNull = fresh("is-null-branch", l -> l.addWrite(tmp, IntLiteral.v(0)));
      // if it is not null, then interrogate the runtime tag.
      InstructionStream isInhabited = fresh("non-null-branch", l -> {
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

  private static String getParamName(Local param) {
    return String.format("regnant$in_%s", param.getName());
  }

  private void translateMethod(InstructionStream is, Env e) {
    TreeMap<Local, Binding> env = e.boundVars;

    // TODO: メソッドのはじめの変数定義はデータフロー解析を入れた時点で消すかもしれない
    // Define all variables at the beginning of the method
    for (Local local : b.getLocals()) {
      if (local.getType() instanceof ArrayType) {
        is.addBinding(local.getName(), new NewArray(new IntLiteral(0)), true);
      } else if (local.getType() instanceof RefLikeType) {
        // Define as null if it is an instance of a class
        is.addBinding(local.getName(), new NullConstant(), true);
      }
      else {
        // TODO: assertion error型等は省いたほうが良さそう
        is.addBinding(local.getName(), new IntLiteral(0), true);
      }
    }

    // Call the basic block at the beginning of the method
    is.addExpr(new InterBasicBlockCall(b, bbm.getEntryPoint(), getMangledName()));
    is.close();

    for (BasicBlock bb : bbg) {
      // TODO: 引数のリストを最適化する
      // TODO: 関数名を自動で生成するようにする
      List<String> arguments = Stream.concat(
              b.getParameterLocals().stream().map(Translate::getParamName),
              b.getLocals().stream().map(Local::getName)
      ).collect(Collectors.toList());

      if (!b.getMethod().isStatic()) {
        arguments.add(0, THIS_PARAM);
      }

      is.addSideFunction(getMangledName() + bb.getId(), arguments, encodeBasicBlock(bb, env));
    }
  }

  /*
    Encodes a basic block into the stream str. In come cases, the final element of the stream may need special handling or must be skipped.
    This is done with the extractFinal and o argument. If the extract final returns null, then it indicates it wants
    the final unit to be translated. In either event, value extracted with extractFinal is then passed to o
   */
  private InstructionStream encodeBasicBlock(final BasicBlock bb, TreeMap<Local, Binding> env) {
    System.out.println("Encoding " + bb);
    List<Unit> units = bb.units;

    InstructionStream is = fresh("BasicBlock");

    for (Unit unit : units) {
      encodeInstruction(is, unit, env, bb);
    }

    // If there is no instruction at the end to explicitly jump between basic blocks, add one.
    if (!(units.get(units.size() - 1) instanceof IfStmt ||
            units.get(units.size() - 1) instanceof GotoStmt ||
            units.get(units.size() - 1) instanceof ReturnStmt ||
            units.get(units.size() - 1) instanceof ReturnVoidStmt)) {
      List<BasicBlock> nextBBs = bbg.getSuccsOf(bb);
      assert (nextBBs.size() == 1);
      BasicBlock nextBB = nextBBs.get(0);

      is.addExpr(new InterBasicBlockCall(b, nextBB, getMangledName()));
    }

    is.close();

    return is;
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
