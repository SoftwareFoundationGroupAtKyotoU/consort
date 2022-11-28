package edu.kyoto.fos.regnant.ir.stmt;

public class AssertFalse extends Effect {
  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("assert(0 = 1)");
  }
}
