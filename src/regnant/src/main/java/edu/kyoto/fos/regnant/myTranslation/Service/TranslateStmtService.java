package edu.kyoto.fos.regnant.myTranslation.Service;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.translatedStmt.*;
import soot.ArrayType;
import soot.Unit;
import soot.jimple.internal.*;

import java.util.List;

// Stmt を場合分けして変換するためのクラス
public class TranslateStmtService {
	// Stmt を場合分けして変換するメソッド
	public TranslatedUnit translate(Unit unit, boolean headOfFunction, List<BasicBlock> nextTranslateBlock, String funcName) {
		// Java SE 12 以降も使えるようにしたら switch 文に書き換える
		if (unit instanceof JNopStmt) {
			// nop の場合 (assert が失敗した場合)
			return new AssertFail();
		} else if (unit instanceof JReturnVoidStmt) {
			// 何も返さない return 文の場合
			return new ReturnVoid();
		} else if (unit instanceof JReturnStmt) {
			// 値を返す return 文の場合
			return new Return((JReturnStmt) unit);
		} else if (unit instanceof JIdentityStmt) {
			// メソッドの引数は IdentityStmt で定義されるからその情報を argument に入れる
			return new Argument((JIdentityStmt) unit);
		} else if (unit instanceof JAssignStmt) {
			// 代入文の場合
			JAssignStmt assignUnit = (JAssignStmt) unit;
			if (assignUnit.getRightOp() instanceof JNewArrayExpr) {
				// 配列を新しく作る場合
				return new NewArray(assignUnit);
			} else if (assignUnit.getLeftOp() instanceof JArrayRef) {
				// 配列の要素を更新する場合
				return new AssignToArray(assignUnit);
			} else if (assignUnit.getRightOp().getType() instanceof ArrayType) {
				// 配列を代入する場合
				return new AssignArrayToV(assignUnit);
			} else if (assignUnit.getLeftOp() instanceof JimpleLocal) {
				// 定義されている変数に値を代入する場合（変数定義は全て初めに行われる）
				return new AssignToVariable(assignUnit);
			} else {
				// throw new RuntimeException("This AssignStmt is not yet supported: " + unit + " ( Left: " + assignUnit.getLeftOp().getClass().toString() + " Right: " + assignUnit.getRightOp().getClass().toString() + ")");
				// デバッグのための, エラーの代わりの標準出力
				return new NotSupportedAssignStmt(assignUnit);
			}
		} else if (unit instanceof JIfStmt) {
			// if 文の場合
			return new If((JIfStmt) unit, nextTranslateBlock, funcName);
		} else if (unit instanceof JGotoStmt) {
			// Goto 文の場合
			return new Goto((JGotoStmt) unit, nextTranslateBlock, funcName);
		} else if (unit instanceof JInvokeStmt) {
			// 関数呼び出しの場合
			return new FunctionCall((JInvokeStmt) unit);
		} else {
			// throw new RuntimeException("This unit is not yet supported: " + unit + " (" + unit.getClass() + ")");
			// デバッグのための, エラーのための標準出力
			return new NotSupportedUnit(unit);
		}
	}
}
