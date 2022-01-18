package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;

import java.util.HashMap;
import java.util.List;

// assert 文が失敗する場合に到達する式を表すクラス
public class AssertFail implements TranslatedUnit {
	public boolean isSequencing() {
		return true;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		return ("assert(0 = 1);");
	}
}
