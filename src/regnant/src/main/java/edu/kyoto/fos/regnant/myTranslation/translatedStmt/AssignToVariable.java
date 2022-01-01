package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.translatedExpr.IntConst;
import soot.jimple.IntConstant;
import soot.jimple.internal.JAssignStmt;

import java.util.List;

// 変数に値を代入する式を表すクラス
public class AssignToVariable implements TranslatedUnit {
	// variable は代入される変数の名前, value は代入する値
	private final String variable;
	private final TranslatedValue value;

	public AssignToVariable(JAssignStmt unit) {
		TranslateExprService handler = new TranslateExprService();

		this.variable = unit.getLeftOp().toString();
		this.value = handler.translate(unit.getRightOp());
	}

	public boolean isSequencing() {
		return true;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder
				.append(variable)
				.append(" := ")
				.append(value.print(true))
				.append(";");

		return builder.toString();
	}

	public String getAssignedVariable() {
		return variable;
	}
}
