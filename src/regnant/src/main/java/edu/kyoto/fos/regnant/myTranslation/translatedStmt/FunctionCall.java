package edu.kyoto.fos.regnant.myTranslation.translatedStmt;

import edu.kyoto.fos.regnant.myTranslation.Service.TranslateExprService;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import edu.kyoto.fos.regnant.myTranslation.translatedExpr.StaticInvoke;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JStaticInvokeExpr;

import java.util.HashMap;
import java.util.List;

// 変換された InvokeStmt を表すクラス
public class FunctionCall implements TranslatedUnit {
	// func は関数呼び出し部分を表す
	private final TranslatedValue func;

	public FunctionCall(JInvokeStmt unit) {
		TranslateExprService service = new TranslateExprService();

		// 今のところは InvokeStmt は JStaticInvokeExpr しか持たないと思っている
		assert (unit.getInvokeExpr() instanceof JStaticInvokeExpr);
		this.func = service.translate(unit.getInvokeExpr());
		assert (func instanceof StaticInvoke);
	}

	public boolean isSequencing() {
		return true;
	}

	public boolean istTranslatedUnitEmpty() {
		return false;
	}

	public String print(List<String> arguments, HashMap<String, Integer> headIDs) {
		return func.print(false, headIDs) + ";";
	}
}
