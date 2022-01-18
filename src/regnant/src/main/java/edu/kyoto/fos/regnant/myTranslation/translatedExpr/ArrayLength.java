package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.Value;
import soot.jimple.internal.JLengthExpr;

import java.util.HashMap;

public class ArrayLength implements TranslatedValue {
	private final Value arrayName;

	public ArrayLength(JLengthExpr e) {
		this.arrayName = e.getOp();
	}

	public String print(boolean isDereference, HashMap<String, Integer> headIDs) {
		StringBuilder builder = new StringBuilder();
		builder
				.append(arrayName.toString())
				.append(".length");

		return builder.toString();
	}
}
