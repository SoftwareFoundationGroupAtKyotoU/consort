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
		// TODO: ここで健全じゃなくなってる. * を付けるかどうかを外す？ それとも最初に変数を全て定義するのが悪い？
		builder
				.append("*")
				.append(arrayName.toString())
				.append(".length");

		return builder.toString();
	}
}
