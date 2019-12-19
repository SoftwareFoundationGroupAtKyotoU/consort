package edu.kyoto.fos.regnant.translation;

import fj.P;
import fj.P2;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public final class FlagTranslation {
  private static int counter = 1;
  private static Map<String, P2<List<Integer>, Boolean>> flags = new HashMap<>();
  private static final String FMT = "regnant$flag_%d";
  public static String allocate(List<Integer> l) {
    return allocate(l, false);
  }

  public static String allocate(final List<Integer> l, final boolean b) {
    String nm = String.format(FMT, counter++);
    flags.put(nm, P.p(new ArrayList<>(l), b));
    return nm;
  }

  public static void outputTo(final String flagsFile) {
    try(PrintStream ps = new PrintStream(new FileOutputStream(new File(flagsFile)))) {
      ps.println("(");
      for(var kv : flags.entrySet()) {
        ps.print("(");
        // extremely unsafe
        ps.print(kv.getKey());
        ps.print(" ");
        assert kv.getValue()._1().size() > 0;
        String keys = kv.getValue()._1().stream().map(Object::toString).collect(Collectors.joining(" ", "(", ")"));
        ps.print(keys);
        ps.print(" ");
        ps.print(kv.getValue()._2() ? "true" : "false");
        ps.println(")");
      }
      ps.println(")");
    } catch (IOException ignore) {

    }
  }
}
