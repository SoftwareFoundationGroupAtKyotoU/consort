package edu.kyoto.fos.regnant.translation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public final class FlagTranslation {
  private static int counter = 1;
  private static Map<String, List<Integer>> flags = new HashMap<>();
  private static final String FMT = "_regnant_flag_%d";
  public static String allocate(List<Integer> l) {
    String nm = String.format(FMT, counter++);
    flags.put(nm, new ArrayList<>(l));
    return nm;
  }
}
