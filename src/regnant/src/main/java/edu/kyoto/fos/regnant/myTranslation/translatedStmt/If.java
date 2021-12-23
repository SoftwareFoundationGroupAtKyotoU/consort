package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JIfStmt;

import java.util.List;

// 変換後の if 式を表すクラス
public class If implements TranslatedUnit {
	// condition は条件式, thenBasicBlock は条件が成り立つ場合, elseBasicBlock は条件式が成田立たない場合を表す
	private final TranslatedValue condition;
	private final BasicBlock thenBasicBlock;
	private final BasicBlock elseBasicBlock;

	public If(JIfStmt unit, List<BasicBlock> nextBasicBlocks) {
		TranslateExprService service = new TranslateExprService();

		this.condition = service.translate(unit.getCondition());

		assert (nextBasicBlocks.size() == 2);
		if (unit.getTarget() == nextBasicBlocks.get(0).getHead()) {
			this.thenBasicBlock = nextBasicBlocks.get(0);
			this.elseBasicBlock = nextBasicBlocks.get(1);
		} else {
			this.thenBasicBlock = nextBasicBlocks.get(1);
			this.elseBasicBlock = nextBasicBlocks.get(0);
		}
	}

	public boolean isSequencing() {
		return false;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder
				.append("if ")
				.append(condition.print(true))
				.append(" then ")
				.append(toFunctionCall(thenBasicBlock, arguments))
				.append(" else ")
				.append(toFunctionCall(elseBasicBlock, arguments));

		return builder.toString();
	}
}
