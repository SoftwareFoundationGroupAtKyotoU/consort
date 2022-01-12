package edu.kyoto.fos.regnant.myTranslation.Service;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.TranslatedUnit;
import edu.kyoto.fos.regnant.myTranslation.translatedStmt.*;
import soot.ArrayType;
import soot.Unit;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JimpleLocal;

import java.util.List;

// Stmt を場合分けして変換するためのクラス
public class TranslateStmtService {
	// Stmt を場合分けして変換するメソッド
	public TranslatedUnit translate(Unit unit, boolean headOfFunction, List<BasicBlock> nextTranslateBlock) {
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
				// 配列の要素を更新する場合 (もし初期化の場合のみ <- を使うとかだったら要修正)
				return new AssignToArray(assignUnit);
			} else if (assignUnit.getLeftOp() instanceof JimpleLocal) {
				if (assignUnit.getLeftOp().toString().contains("tmp")) {
					// 定義する変数が tmp 変数の場合
					return new NewTmpVariable(assignUnit);
				} else if (headOfFunction) {
					// 初めて変数が定義される場合 (関数の中の最初の基本ブロックに変数定義が全て含まれているという仮説による)
					if (assignUnit.getRightOp().getType() instanceof ArrayType) {
						// 右辺が配列の場合
						return new NewPrimitiveVariable(assignUnit);
					} else {
						return new NewRef(assignUnit);
					}
				}  else {
					// 定義されている変数に値を代入する場合
					return new AssignToVariable(assignUnit);
				}
			} else {
				// throw new RuntimeException("This AssignStmt is not yet supported: " + unit + " ( Left: " + assignUnit.getLeftOp().getClass().toString() + " Right: " + assignUnit.getRightOp().getClass().toString() + ")");
				// デバッグのための, エラーの代わりの標準出力
				return new NotSupportedAssignStmt(assignUnit);
			}
		} else if (unit instanceof JIfStmt) {
			// if 文の場合
			return new If((JIfStmt) unit, nextTranslateBlock);
		} else if (unit instanceof JGotoStmt) {
			// Goto 文の場合
			return new Goto((JGotoStmt) unit, nextTranslateBlock);
		} else {
			// TODO: InvokeStmt にも対応する
			// throw new RuntimeException("This unit is not yet supported: " + unit + " (" + unit.getClass() + ")");
			// デバッグのための, エラーのための標準出力
			return new NotSupportedUnit(unit);
		}
	}
}
