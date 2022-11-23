package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;

public class Return extends Effect {
	// TODO: valの型がこれでいいか考える
	private final ImpExpr val;

	public Return(final ImpExpr val) {
		this.val = val;
	}

	@Override public void printAt(final int level, final StringBuilder b) {
		indent(level, b).append("return ");
		this.val.printOn(b);
	}
}
