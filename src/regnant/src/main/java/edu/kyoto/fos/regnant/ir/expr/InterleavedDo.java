package edu.kyoto.fos.regnant.ir.expr;

import java.util.Iterator;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.stream.Stream;

public interface InterleavedDo {
  default <R, U> void doInterleaved(Stream<R> stream, U init, BiConsumer<R, U> each, Consumer<U> sep) {
    Iterator<R> it = stream.iterator();
    boolean first = true;
    while(it.hasNext()) {
      if(!first) {
        sep.accept(init);
      }
      first = false;
      R item = it.next();
      each.accept(item, init);
    }
  }
}
