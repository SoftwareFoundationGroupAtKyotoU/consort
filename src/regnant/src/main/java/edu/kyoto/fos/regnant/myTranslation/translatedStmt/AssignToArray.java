package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;

import java.util.HashMap;
import java.util.List;

// 配列に代入する式を表すクラス
public class AssignToArray implements TranslatedUnit {
	// arrayName は配列名, index は配列の中の代入されるインデックス, value は代入される値を表す
	private final String arrayName;
	private final TranslatedValue index;
	private final TranslatedValue value;

	public AssignToArray(JAssignStmt unit) {
		TranslateExprService service = new TranslateExprService();

		this.arrayName = ((JArrayRef) (unit.getLeftOp())).getBase().toString();
		this.index = service.translate(((JArrayRef) (unit.getLeftOp())).getIndex());
		this.value = service.translate(unit.getRightOp());
	}

	public boolean isSequencing() {
		return true;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		StringBuilder builder = new StringBuilder();
		builder
				.append(arrayName)
				.append("[")
				.append(index.print(true, headIDs))
				.append("] <- ")
				.append(value.print(true, headIDs))
				.append(";");

		return builder.toString();
	}
}
