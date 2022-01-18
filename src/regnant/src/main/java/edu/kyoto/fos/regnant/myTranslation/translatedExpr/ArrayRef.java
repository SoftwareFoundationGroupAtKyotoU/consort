package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JArrayRef;

import java.util.HashMap;

public class ArrayRef implements TranslatedValue {
	// arrayName は配列名, index は配列の中の代入されるインデックスを表す
	private final String arrayName;
	private final TranslatedValue index;

	public ArrayRef(JArrayRef e) {
		TranslateExprService service = new TranslateExprService();

		this.arrayName = e.getBase().toString();
		this.index = service.translate(e.getIndex());
	}

	public String print(boolean isDereference, HashMap<String, Integer> headIDs) {
		StringBuilder builder = new StringBuilder();
		builder
				.append(arrayName)
				.append("[")
				.append(index.print(true, headIDs))
				.append("]");

		return builder.toString();
	}
}
