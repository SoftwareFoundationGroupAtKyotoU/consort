package edu.kyoto.fos.regnant.myTranslation.Service;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import edu.kyoto.fos.regnant.myTranslation.translatedExpr.*;

import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.internal.*;

// Expr を場合分けするためのクラス
public class TranslateExprService {
	// Expr を場合分けして変換するメソッド
	public TranslatedValue translate(Value value) {
		if (value instanceof JAddExpr) {
			return new Add((JAddExpr) value);
		} else if (value instanceof JMulExpr) {
			return new Mult((JMulExpr) value);
		} else if (value instanceof JRemExpr) {
			return new Rem((JRemExpr) value);
		} else if (value instanceof JEqExpr) {
			return new Eq((JEqExpr) value);
		} else if (value instanceof JGeExpr) {
			return new Ge((JGeExpr) value);
		} else if (value instanceof JNeExpr) {
			return new NotEq((JNeExpr) value);
		} else if (value instanceof JGtExpr) {
			return new Gt((JGtExpr) value);
		} else if (value instanceof JLeExpr) {
			return new Le((JLeExpr) value);
		} else if (value instanceof JLtExpr) {
			return new Lt((JLtExpr) value);
		} else if (value instanceof JimpleLocal) {
			return new Variable((JimpleLocal) value);
		} else if (value instanceof JLengthExpr) {
			return new ArrayLength((JLengthExpr) value);
		} else if (value instanceof JArrayRef) {
			return new ArrayRef((JArrayRef) value);
		} else if (value instanceof IntConstant) {
			return new IntConst(value.toString());
		} else if (value instanceof JStaticInvokeExpr) {
			return new StaticInvoke((JStaticInvokeExpr) value);
		} else {
			return new Other(value);
		}
	}
}
