package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.Value;
import soot.jimple.internal.JReturnStmt;

import java.util.HashMap;
import java.util.List;

// ある値を返す return 文のクラス
public class Return implements TranslatedUnit {
	// returnValue は返り値
	private final TranslatedValue returnValue;

	public Return(JReturnStmt unit) {
		TranslateExprService service = new TranslateExprService();

		this.returnValue = service.translate(unit.getOp());
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
				.append("return ")
				.append(returnValue.print(true, headIDs));

		return builder.toString();
	}
}