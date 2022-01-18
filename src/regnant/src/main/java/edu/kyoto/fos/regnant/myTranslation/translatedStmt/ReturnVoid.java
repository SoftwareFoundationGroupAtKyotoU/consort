package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;

import java.util.HashMap;
import java.util.List;

// 何の値も返さない return 文を表すクラス
public class ReturnVoid implements TranslatedUnit {

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	// 出力する際には0を返すようにする
	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		return "return 0";
	}
}