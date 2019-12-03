package edu.kyoto.fos.regnant;

public interface Printable {
  void printAt(int level, StringBuilder b);
  default StringBuilder indent(int i, StringBuilder b) {
    for(int j = 0; j < i; j++) {
      b.append("  ");
    }
    return b;
  }
}
