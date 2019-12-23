package edu.kyoto.fos.regnant.ir.stmt.aliasing;

import edu.kyoto.fos.regnant.ir.expr.ProgFragment;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.stream.Stream;

public class AliasOp implements ProgFragment {

  private final String root;
  private final List<ApElem> elems;

  public AliasOp(final String root, final List<ApElem> elems) {
    this.root = root;
    this.elems = elems;
  }

  public static Builder buildAt(String v) {
    return new Builder(v);
  }

  @Override public void printOn(final StringBuilder sb) {
    String it = this.root;
    for(ApElem e : this.elems) {
      String pre = it;
      it = e.extendWith(it);
    }
    sb.append(it);
  }

  public static class Builder {
    private final String root;
    private List<ApElem> elem = new ArrayList<>();

    private Builder(String root) {
      this.root = root;
    }

    public Builder proj(int i) {
      elem.add(new Proj(i));
      return this;
    }

    public Builder deref() {
      elem.add(Deref.v);
      return this;
    }

    public AliasOp build() {
      return new AliasOp(root, elem);
    }

    public <A> Builder iter(Stream<A> cons, BiConsumer<A, Builder> act) {
      cons.forEachOrdered(a -> act.accept(a, this));
      return this;
    }
  }

  @Override public String toString() {
    return root + "." + elems;
  }

  public static AliasOp of(String root, ApElem... elems) {
    return new AliasOp(root, Arrays.asList(elems));
  }

  public static AliasOp var(String root) {
    return new AliasOp(root, Collections.emptyList());
  }
}
