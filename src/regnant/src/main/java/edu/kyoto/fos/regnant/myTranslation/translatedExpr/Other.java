package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.Value;

import java.util.HashMap;

// その他の Expr を表すクラス
public class Other implements TranslatedValue {
	// value は Expr そのものを表す
	private final Value value;

	public Other(Value value) {
		this.value = value;
	}

	// 元々の toString をそのまま返す
	public String print(boolean isPointer, HashMap<String, Integer> headIDs) {
		return value.toString();
	}
}
