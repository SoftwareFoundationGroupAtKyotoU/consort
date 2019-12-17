package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.stmt.Alias;
import edu.kyoto.fos.regnant.ir.stmt.ArrayWrite;
import edu.kyoto.fos.regnant.ir.stmt.AssertFalse;
import edu.kyoto.fos.regnant.ir.stmt.Assign;
import edu.kyoto.fos.regnant.ir.stmt.Bind;
import edu.kyoto.fos.regnant.ir.stmt.Block;
import edu.kyoto.fos.regnant.ir.stmt.Condition;
import edu.kyoto.fos.regnant.ir.stmt.Effect;
import edu.kyoto.fos.regnant.ir.stmt.LetBind;
import edu.kyoto.fos.regnant.ir.stmt.NullCheck;
import edu.kyoto.fos.regnant.ir.stmt.SideEffect;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasVar;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.Ptr;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.PtrProj;
import fj.P;
import fj.P3;
import soot.Local;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class InstructionStream implements Printable  {

  private final String tag;
  public List<P3<String, List<String>, InstructionStream>> sideFunctions = new ArrayList<>();

  public InstructionStream(final String tag) {
    this.tag = tag;
  }

  public static InstructionStream fresh(String tag) {
    return new InstructionStream(tag);
  }

  public static InstructionStream fresh(String tag, Consumer<InstructionStream> init) {
    InstructionStream l = fresh(tag);
    init.accept(l);
    return l;
  }

  public void addBinding(String name, ImpExpr rhs, boolean ref) {
    this.addBind(new LetBind(name, rhs, ref));
  }

  public void printAt(final int level, final StringBuilder sb) {
    assert this.isTerminal() : sb.toString() + " " + this.tag;
    printLoop(level, sb, this.stateStack.iterator());
  }

  private void printLoop(final int level, final StringBuilder sb, final Iterator<StreamState> iterator) {
    if(!iterator.hasNext()) {
      this.termNode.printAt(level, sb);
      return;
    }
    StreamState st = iterator.next();
    int bodyLevel = st.open(level, sb);
    st.printAt(bodyLevel, sb);
    printLoop(bodyLevel, sb, iterator);
    st.close(level, sb);
  }

  public InstructionStream andClose() {
    this.close();
    return this;
  }

  public void addAssertFalse() {
    this.addEffect(new AssertFalse());
  }

  public void addAlias(final String name, final String paramName) {
    this.addEffect(new Alias(name, new AliasVar(paramName)));
  }

  public void addExpr(final ImpExpr expr) {
    this.addEffect(new SideEffect(expr));
  }

  public void addArrayWrite(final ImpExpr basePtr, final ImpExpr ind, final ImpExpr val) {
    this.addEffect(new ArrayWrite(basePtr, ind, val));
  }

  private abstract static class StreamState implements Printable {
    public abstract StreamState addBind(Bind b, LinkedList<StreamState> state);
    public abstract StreamState addEffect(Effect b, LinkedList<StreamState> state);

    public abstract Term unit(final LinkedList<StreamState> stateStack);
    protected abstract boolean isPopulated();
    public void onRet(List<StreamState> s) {
      if(isPopulated()) {
        s.add(this);
      }
    }

    public abstract int open(final int level, final StringBuilder sb);
    public abstract void close(final int level, final StringBuilder sb);
    @Override public String toString() {
      StringBuilder sb = new StringBuilder();
      this.printAt(0, sb);
      return "[" + sb.toString() + "]";
    }
  }

  private static class SideEffectState extends StreamState {
    ArrayList<Effect> currEffects = new ArrayList<>();

    public SideEffectState(final Effect b) {
      this.currEffects.add(b);
    }

    @Override
    public StreamState addEffect(Effect e, LinkedList<StreamState> state) {
      currEffects.add(e);
      return this;
    }

    @Override public Term unit(final LinkedList<StreamState> stateStack) {
      stateStack.add(this);
      return new Skip();
    }

    @Override protected boolean isPopulated() {
      return !currEffects.isEmpty();
    }

    @Override public int open(final int level, final StringBuilder sb) {
      indent(level, sb).append("{\n");
      return level + 1;
    }

    @Override public void close(final int level, final StringBuilder sb) {
      indent(level, sb).append("}\n");
    }

    @Override public void printAt(final int bodyLevel, final StringBuilder sb) {
      currEffects.forEach(e -> {
        e.printAt(bodyLevel, sb);
        sb.append(";\n");
      });
    }

    public StreamState addBind(Bind b, LinkedList<StreamState> state) {
      if(currEffects.size() > 0) {
        state.add(this);
      }
      return new BindState(b);
    }
  }

  private static class BindState extends StreamState {
    ArrayList<Bind> binds = new ArrayList<>();
    public BindState(final Bind b) {
      this.binds.add(b);
    }

    public BindState() {
    }

    @Override public StreamState addBind(final Bind b, final LinkedList<StreamState> state) {
      binds.add(b);
      return this;
    }

    @Override public StreamState addEffect(final Effect b, final LinkedList<StreamState> state) {
      if(binds.size() > 0) {
        state.add(this);
      }
      return new SideEffectState(b);
    }

    @Override public Term unit(final LinkedList<StreamState> stateStack) {
      if(binds.size() > 0) {
        stateStack.add(this);
      }
      return new Unit();
    }

    @Override protected boolean isPopulated() {
      return !binds.isEmpty();
    }

    @Override public int open(final int level, final StringBuilder sb) {
      return level;
    }

    @Override public void close(final int level, final StringBuilder sb) {

    }

    @Override public void printAt(final int level, final StringBuilder sb) {
      binds.forEach(b -> {
        b.printAt(level, sb);
        sb.append("\n");
      });
    }
  }

  private final LinkedList<StreamState> stateStack = new LinkedList<>();
  private Term termNode = null;
  private StreamState state = new BindState();

  private static abstract class Term implements Printable {}
  private static class Unit extends Term {
    @Override public void printAt(final int level, final StringBuilder sb) {
      indent(level, sb).append("()");
    }
  }

  private static class Return extends Term {
    private final ImpExpr returnOp;

    private Return(final ImpExpr returnOp) {
      assert returnOp != null;
      this.returnOp = returnOp;
    }

    @Override public void printAt(int level, StringBuilder sb) {
      indent(level, sb).append("return ");
      returnOp.printOn(sb);
      sb.append("\n");
    }
  }

  private static class Skip extends Term {
    @Override public void printAt(final int level, final StringBuilder b) {
      // don't print, anything
    }
  }

  private void addEffect(Effect b) {
    assert !this.isTerminal() : System.identityHashCode(this);
    this.state = this.state.addEffect(b, this.stateStack);
  }

  private void addBind(Bind b) {
    assert !this.isTerminal(): System.identityHashCode(this);
    this.state = this.state.addBind(b, this.stateStack);
  }

  public void addWrite(String name, ImpExpr val) {
    this.addEffect(new Assign(name, val));
  }

  public void addCond(ImpExpr cond, InstructionStream tr, InstructionStream fls) {
    tr.close();
    fls.close();
    this.inheritFunctions(tr);
    this.inheritFunctions(fls);
    this.addEffect(new Condition(cond, tr, fls));
  }

  public void addNullCond(final ImpExpr value, final InstructionStream tBranch, final InstructionStream falseBranch) {
    tBranch.close();
    falseBranch.close();
    this.inheritFunctions(tBranch);
    this.inheritFunctions(falseBranch);
    this.addEffect(new NullCheck(value, tBranch, falseBranch));
  }

  public void addBlock(final InstructionStream is) {
    this.inheritFunctions(is);
    is.close();
    if(is.termNode instanceof Skip && is.stateStack.size() == 1 && is.stateStack.peekFirst() instanceof SideEffectState) {
      SideEffectState effects = (SideEffectState) is.stateStack.peekFirst();
      effects.currEffects.forEach(this::addEffect);
    } else {
      this.addEffect(new Block(is));
    }
  }

  public void addPtrAlias(final String base, final String ptrVar) {
    this.addEffect(new Alias(base, new Ptr(ptrVar)));
  }

  public void addPtrProjAlias(final String fieldTemp, final String fieldBase, final int slot) {
    this.addEffect(new Alias(fieldTemp, new PtrProj(fieldBase, slot)));
  }

  public void bindProjection(final String fieldTemp, final int slot, final int slotOf, final String fieldBase) {
    this.addBind(new Bind() {
      @Override public void printAt(final int level, final StringBuilder b) {
        Stream.Builder<String> builder = Stream.builder();
        for(int i = 0; i < slot; i++) {
          builder.add("_");
        }
        builder.add(fieldTemp);
        for(int i = slot + 1; i < slotOf; i++) {
          builder.add("_");
        }
        String bind = builder.build().collect(Collectors.joining(", ", "(", ")"));
        indent(level, b).append("let ").append(bind).append(" = *").append(fieldBase).append(" in ");
      }
    });
  }

  private void inheritFunctions(final InstructionStream fls) {
    this.sideFunctions.addAll(fls.sideFunctions);
  }

  public static InstructionStream unit(String tag) {
    InstructionStream i = new InstructionStream(tag);
    i.close();
    return i;
  }

  public void ret(ImpExpr val) {
    this.state.onRet(this.stateStack);
    this.termNode = new Return(val);
  }

  public void returnUnit() {
    this.ret(ImpExpr.unitValue());
  }

  public void addSideFunction(String name, List<String> l, InstructionStream s) {
    this.inheritFunctions(s);
    this.sideFunctions.add(P.p(name, l, s));
  }

  public void addSideFunction(String name, Collection<Local> l, InstructionStream s) {
    this.addSideFunction(name, l.stream().map(Local::getName).collect(Collectors.toList()), s);

  }

  public void addLoopInvoke(String name, List<Local> args) {
    this.addEffect(SideEffect.loop(name, args));
  }

  public void setControl(final int coordId) {
    this.addWrite(Translate.CONTROL_FLAG, ImpExpr.literalInt(coordId));
  }

  public boolean isTerminal() {
    return this.termNode != null;
  }

  public void close() {
    if(!this.isTerminal()) {
      this.termNode = this.state.unit(this.stateStack);
    }
  }

  public StringBuilder dumpAs(String name, List<String> locals) {
    StringBuilder sb = new StringBuilder();
    sb.append(name).append(locals.stream().collect(Collectors.joining(",", "(", ")")));
    sb.append("{\n");
    this.printAt(1, sb);
    sb.append("\n}\n");
    return sb;
  }
}
