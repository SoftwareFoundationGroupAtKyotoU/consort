package edu.kyoto.fos.regnant.myTranslation.translatedExpr;

import edu.kyoto.fos.regnant.myTranslation.TranslatedValue;
import soot.jimple.internal.JStaticInvokeExpr;

import java.util.stream.Collectors;

public class StaticInvoke implements TranslatedValue {
	JStaticInvokeExpr func;

	public StaticInvoke(JStaticInvokeExpr e) {
		this.func = e;
	}

	public String print(boolean isDereference) {
		String arguments = func.getArgs().stream().map(Object::toString).collect(Collectors.joining(", "));

		StringBuilder sb = new StringBuilder();
		sb
				.append(func.getMethod().getName())
				.append("(")
				.append(arguments)
				.append(")");
		return sb.toString();
	}
}

