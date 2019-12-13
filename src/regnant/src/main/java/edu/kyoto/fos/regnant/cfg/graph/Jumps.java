package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.cfg.AnnotatedEdge;
import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.cfg.Loop;
import fj.P;
import fj.P2;

import java.util.Comparator;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Jumps {
  Comparator<P2<Coord, BasicBlock>> cmp = Comparator
      .comparing((Function<P2<Coord, BasicBlock>, Coord>) P2::_1)
      .thenComparing(P2::_2);

  // A map of coordinates and target location to the loop headers which must be broken
  public Map<P2<Coord, BasicBlock>, Set<BasicBlock>> brk = new TreeMap<>(cmp);
  // A set of coordinates (a jump source) and it's target loop header
  public Set<P2<Coord, BasicBlock>> cont = new TreeSet<>(cmp);
  // A set of coordinates (jump source) and it's target basic block
  public Set<P2<Coord, BasicBlock>> flow = new TreeSet<>(cmp);

  public static Jumps ret(BasicBlock b) {
    return new Jumps();
  }

  public static Jumps of(Coord c, final AnnotatedEdge succ) {
    Jumps toRet = new Jumps();
    toRet.update(c, succ);
    return toRet;
  }

  public void update(final Coord c, final AnnotatedEdge succ) {
    if(succ.cont.isPresent() && succ.brk.isEmpty()) {
      cont.add(P.p(c, succ.cont.get().getHeader()));
    } else if(!succ.brk.isEmpty()) {
      brk.put(P.p(c, succ.block), succ.brk.stream().map(Loop::getHeader).collect(Collectors.toSet()));
    } else {
      assert succ.brk.isEmpty();
      assert !succ.cont.isPresent();
      flow.add(P.p(c, succ.block));
    }
  }

  public static Jumps jumpTo(Coord c, final BasicBlock block) {
    Jumps j = new Jumps();
    j.flow.add(P.p(c, block));
    return j;
  }

  public Jumps union(final Jumps jumps) {
    Jumps j = new Jumps();
    j.mergeIn(this);
    j.mergeIn(jumps);
    return j;
  }

  public void mergeIn(final Jumps j_) {
    this.flow.addAll(j_.flow);
    this.cont.addAll(j_.cont);
    j_.brk.forEach((k,v) -> this.brk.merge(k, v, (old, up) -> {
      Set<BasicBlock> hds = new HashSet<>(old);
      hds.addAll(up);
      return hds;
    }));
  }

  @Override public String toString() {
    String s = Stream.concat(this.brk.keySet().stream(),
        Stream.concat(this.flow.stream(), this.cont.stream())
    ).map(P2::_2).map(b -> String.valueOf(b.getId()))
      .reduce((a, b) -> a + ", " + b).orElse("");
    return "[goto: {" + s + "}; brk: " + brk + "]";
  }
}
