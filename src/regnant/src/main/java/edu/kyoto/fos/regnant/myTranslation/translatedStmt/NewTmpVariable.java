package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JAssignStmt;

import java.util.List;

public class NewTmpVariable implements TranslatedUnit {
	// variable は定義する変数の名前, value は変数を初期化する値
	private final String variable;
	private final TranslatedValue value;

	public NewTmpVariable(JAssignStmt unit) {
		TranslateExprService service = new TranslateExprService();

		this.variable = unit.getLeftOp().toString();
		this.value = service.translate(unit.getRightOp());
	}

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder
				.append("let ")
				.append(variable)
				.append(" = ")
				.append(value.print(false))
				.append(" in");

		return builder.toString();
	}
}
