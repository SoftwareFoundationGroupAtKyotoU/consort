package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.jimple.internal.JGotoStmt;

import java.util.HashMap;
import java.util.List;

// 変換後の Goto 式を表すクラス
public class Goto implements TranslatedUnit {
	// funcName は現在制御が渡っている元々の関数名, target は Goto で向かう基本ブロックを表す.
	private final String funcName;
	private final BasicBlock target;

	public Goto(JGotoStmt unit, List<BasicBlock> nextBasicBlocks, String funcName) {
		this.funcName = funcName;

		assert (nextBasicBlocks.size() == 1);
		this.target = nextBasicBlocks.get(0);
	}

	public boolean isSequencing() {
		return false;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		return toFunctionCall(target, arguments, funcName);
	}
}
