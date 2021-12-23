package edu.kyoto.fos.regnant;

public interface Printable {
  void printAt(int level, StringBuilder b);
  // インデントを加えるメソッド
  default StringBuilder indent(int i, StringBuilder b) {
    for(int j = 0; j < i; j++) {
      b.append("  ");
    }
    return b;
  }
}
