package edu.kyoto.fos.regnant.ir;

public class Assign extends Effect {
  private final String name;
  private final ImpRHS val;

  public Assign(final String name, final ImpRHS val) {
    this.name = name;
    this.val = val;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append(this.name).append(" := ");
    this.val.toSyntax(b);
  }
}
