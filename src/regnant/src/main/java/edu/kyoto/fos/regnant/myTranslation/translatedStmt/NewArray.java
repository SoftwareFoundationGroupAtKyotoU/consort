package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewArrayExpr;

import java.util.HashMap;
import java.util.List;

// 配列を新しく定義する式を表すクラス
public class NewArray implements TranslatedUnit {
	// arrayName は定義する配列の名前, arraySize は配列の大きさ
	public String arrayName;
	public String arraySize;

	public NewArray(JAssignStmt unit) {
		this.arrayName = unit.getLeftOp().toString();
		this.arraySize = ((JNewArrayExpr) (unit.getRightOp())).getSize().toString();
	}

	public NewArray(String arrayName, String arraySize) {
		this.arrayName = arrayName;
		this.arraySize = arraySize;
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
				.append(arrayName)
				.append(" = mkarray ")
				.append(arraySize)
				.append(" in");

		return builder.toString();
	}
}
