package edu.kyoto.fos.regnant.simpl;

import soot.Body;

import java.util.List;
import java.util.function.Function;

public class RewriteChain {
  private static final List<Function<Body, Body>> rewriters = List.of(
      AssertionRewriter::rewrite,
      RandomRewriter::rewriteRandom
  );
  public static Body rewrite(Body b) {
    Body it = b;
    for(var f : rewriters) {
      it = f.apply(it);
    }
    return it;
  }

}
