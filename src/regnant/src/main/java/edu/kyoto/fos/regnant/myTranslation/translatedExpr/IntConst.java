package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.IntConstant;

public class IntConst implements TranslatedValue {
	private final String value;

	public IntConst(String value) {
		this.value = value;
	}

	public String print(boolean isDereference) {
		return value;
	}
}
