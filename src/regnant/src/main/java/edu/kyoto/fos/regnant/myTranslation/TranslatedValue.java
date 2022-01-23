package edu.kyoto.fos.regnant.myTranslation;

import java.util.HashMap;

// 変換後の value (Expr) を表すインターフェース
public interface TranslatedValue {
	// Regnant における抽象構文木から ConSORT プログラムに変換するメソッド
	// isDereference は * を付けるかどうか
	String print(boolean isDereference, HashMap<String, Integer> headIDs);
}