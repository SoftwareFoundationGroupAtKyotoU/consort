package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.translation.InstructionStream;

public class Block extends Effect {
  private final InstructionStream is;

  public Block(final InstructionStream is) {
    this.is = is;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("{\n");
    this.is.printAt(level + 1, b);
    b.append("\n");
    indent(level, b).append("}\n");
  }
}
