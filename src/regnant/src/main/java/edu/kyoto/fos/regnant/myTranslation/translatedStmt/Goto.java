package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import soot.jimple.internal.JGotoStmt;

import java.util.List;

public class Goto implements TranslatedUnit {
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

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments) {
		return toFunctionCall(target, arguments, funcName);
	}
}
