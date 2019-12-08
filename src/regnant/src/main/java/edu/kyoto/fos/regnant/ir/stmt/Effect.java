package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.Printable;

public abstract class Effect implements Printable {
  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    this.printAt(0, sb);
    return sb.toString();
  }
}
