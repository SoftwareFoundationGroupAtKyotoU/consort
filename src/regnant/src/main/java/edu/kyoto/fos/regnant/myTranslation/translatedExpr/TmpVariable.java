package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JimpleLocal;

import java.util.HashMap;

public class TmpVariable implements TranslatedValue {
	// variable は JimpleLocal そのものを表す
	private final JimpleLocal variable;

	public TmpVariable(JimpleLocal variable) {
		this.variable = variable;
	}

	public String print(boolean isDereference, HashMap<String, Integer> headIDs) {
		return variable.toString();
	}
}
