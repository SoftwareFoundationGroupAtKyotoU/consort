package edu.kyoto.fos.regnant.ir.stmt;

import edu.kyoto.fos.regnant.ir.expr.InterBasicBlockCall;

public class Goto extends Effect {
	private final InterBasicBlockCall target;

	public Goto(final InterBasicBlockCall target) {
		this.target = target;
	}

	@Override public void printAt(final int level, final StringBuilder b) {
		this.target.printOn(b);
	}
}
