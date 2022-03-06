package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.Value;
import soot.jimple.internal.JIdentityStmt;

import java.util.HashMap;
import java.util.List;

// 基本ブロックを関数にした際に引数を設定するためのクラス
// 変換後は式としては残らない
public class Argument implements TranslatedUnit {
	// argumentVariable は引数の変数名を表す
	private final String variable;
	private final String parameter;
	private static int id = 0;

	public Argument(JIdentityStmt unit) {
		this.variable = unit.getLeftOp().toString();
		this.parameter = "reg_p_" + id;
		id++;
	}

	public boolean isSequencing() {
		return true;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		StringBuilder builder = new StringBuilder();
		builder
				.append(variable)
				.append(" := ")
				.append(parameter)
				.append(";");

		return builder.toString();
	}

	// 引数を外に伝えるためのメソッド
	public String getArgumentVariable() {
		return parameter;
	}
}
