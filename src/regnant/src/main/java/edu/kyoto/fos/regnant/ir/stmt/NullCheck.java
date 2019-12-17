package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.translation.InstructionStream;

public class NullCheck extends Effect {
  private final ImpExpr value;
  private final InstructionStream trueBranch;
  private final InstructionStream falseBranch;

  public NullCheck(final ImpExpr value, final InstructionStream tBranch, final InstructionStream falseBranch) {
    super();
    this.value = value;
    this.trueBranch = tBranch;
    this.falseBranch = falseBranch;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append("ifnull ");
    value.printOn(b);
    b.append(" then\n");
    trueBranch.printAt(level + 1, b);
    b.append("\n");
    indent(level, b).append("else\n");
    falseBranch.printAt(level + 1, b);
  }
}
