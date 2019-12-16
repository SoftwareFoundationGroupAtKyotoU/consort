package edu.kyoto.fos.regnant.translation;

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
  private static Map<String, List<Integer>> flags = new HashMap<>();
  private static final String FMT = "regnant$flag_%d";
  public static String allocate(List<Integer> l) {
    String nm = String.format(FMT, counter++);
    flags.put(nm, new ArrayList<>(l));
    return nm;
  }

  public static void outputTo(final String flagsFile) {
    try(PrintStream ps = new PrintStream(new FileOutputStream(new File(flagsFile)))) {
      ps.println("(");
      for(Map.Entry<String, List<Integer>> kv : flags.entrySet()) {
        ps.print("(");
        // extremely unsafe
        ps.print(kv.getKey());
        ps.print(" ");
        assert kv.getValue().size() > 0;
        String keys = kv.getValue().stream().map(Object::toString).collect(Collectors.joining(" ", "(", ")"));
        ps.print(keys);
        ps.println(")");
      }
      ps.println(")");
    } catch (IOException ignore) {

    }
  }
}
