package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import soot.jimple.internal.JAssignStmt;

import java.util.HashMap;
import java.util.List;

// 変数を (ポインタで) 定義する式を表すクラス
public class NewRef implements TranslatedUnit {
	// variable は定義する変数の名前, value は変数を初期化する値
	private final String variable;
	private final TranslatedValue value;

	public NewRef(JAssignStmt unit) {
		TranslateExprService service = new TranslateExprService();

		this.variable = unit.getLeftOp().toString();
		this.value = service.translate(unit.getRightOp());
	}

	// 変数定義の追加によって直接 NewRef を作る際に使うコンストラクタ
	public NewRef(String variable, TranslatedValue value) {
		this.variable = variable;
		this.value = value;
	}

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		StringBuilder builder = new StringBuilder();
		builder
				.append("let ")
				.append(variable)
				.append(" = mkref ")
				.append(value.print(true, headIDs))
				.append(" in");

		return builder.toString();
	}

	// 束縛された変数を外に伝えるためのメソッド
	public String getBoundVariable() {
		return variable;
	}
}