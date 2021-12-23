package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.Value;
import soot.jimple.internal.JAssignStmt;

import java.util.List;

// まだ対応できていない JAssignStmt をエラーにする代わりに出力するためのクラス
public class NotSupportedAssignStmt implements TranslatedUnit {
	// unit は変換前の unit, leftOp は変換前の unit の左辺, rightOp は変換前の unit の右辺
	private final JAssignStmt unit;
	private final Value leftOp;
	private final Value rightOp;

	public NotSupportedAssignStmt(JAssignStmt unit) {
		this.unit = unit;
		this.leftOp = unit.getLeftOp();
		this.rightOp = unit.getRightOp();
	}

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	// 出力の際には変換前の unit と, 左辺と右辺それぞれのクラスを出力する
	public String print(List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder
				.append("This AssignStmt is not yet supported: ")
				.append(unit.toString())
				.append(" ( Left: ")
				.append(leftOp.getClass().toString())
				.append(" Right: ")
				.append(rightOp.getClass().toString())
				.append(")");

		return builder.toString();
	}
}
