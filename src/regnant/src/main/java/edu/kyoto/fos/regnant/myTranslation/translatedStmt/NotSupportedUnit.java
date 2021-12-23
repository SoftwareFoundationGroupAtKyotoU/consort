package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.Unit;

import java.util.List;

// まだ対応していない Unit (Statement) をエラーにする代わりに出力するためのクラス
public class NotSupportedUnit implements TranslatedUnit {
	//  unit は変化前の unit
	public Unit unit;

	public NotSupportedUnit(Unit unit) {
		this.unit = unit;
	}

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	// 出力の際には変換前の unit を出力する
	public String print(List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder
				.append("This unit is not yet supported: ")
				.append(unit.toString())
				.append(" (")
				.append(unit.getClass().toString())
				.append(")");

		return builder.toString();
	}
}
