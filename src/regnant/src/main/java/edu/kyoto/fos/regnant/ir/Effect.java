package edu.kyoto.fos.regnant.ir;

import edu.kyoto.fos.regnant.Printable;

public abstract class Effect implements Printable {
  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    this.printAt(0, sb);
    return sb.toString();
  }
}
