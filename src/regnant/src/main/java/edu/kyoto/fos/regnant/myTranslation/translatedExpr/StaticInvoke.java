package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JStaticInvokeExpr;

import java.util.HashMap;
import java.util.stream.Collectors;

public class StaticInvoke implements TranslatedValue {
	JStaticInvokeExpr func;

	public StaticInvoke(JStaticInvokeExpr e) {
		this.func = e;
	}

	public String print(boolean isDereference, HashMap<String, Integer> headIDs) {
		String arguments = func.getArgs().stream().map(Object::toString).map(v -> "*" + v).collect(Collectors.joining(", "));
		String funcName = func.getMethod().getName();

		StringBuilder sb = new StringBuilder();
		sb
				.append(funcName)
				.append("_")
				.append(headIDs.get(funcName))
				.append("(")
				.append(arguments)
				.append(")");
		return sb.toString();
	}
}

