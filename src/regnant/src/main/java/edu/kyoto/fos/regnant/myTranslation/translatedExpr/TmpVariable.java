package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JimpleLocal;

public class TmpVariable implements TranslatedValue {
	// variable は JimpleLocal そのものを表す
	private final JimpleLocal variable;

	public TmpVariable(JimpleLocal variable) {
		this.variable = variable;
	}

	public String print(boolean isDereference) {
		return variable.toString();
	}
}
