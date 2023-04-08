package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.cfg.BasicBlock;
import soot.Body;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static edu.kyoto.fos.regnant.translation.Translate.THIS_PARAM;

public class InterBasicBlockCall extends Call implements Printable {
	private final boolean isStatic;
	private final List<String> paramNamesOfMethod = new ArrayList<>();

	public InterBasicBlockCall(Body b, BasicBlock bb, String calleeName) {
		// TODO: データフロー解析の結果（全体）を第二引数に渡す
		super(calleeName + bb.getId(),
				b.getLocals().stream().map(
						local -> new Variable(local.getName(), false)
				).collect(Collectors.toList())
		);

		this.isStatic = b.getMethod().isStatic();

		for(int i = 0; i < b.getMethod().getParameterCount(); i++) {
			// TODO: 動くけど汚い、TranslateにあるgetParamNameを再利用したい
			paramNamesOfMethod.add(String.format("regnant$in_%s", b.getParameterLocal(i).getName()));
		}
	}

	@Override
	public void printOn(StringBuilder sb) {
		sb.append(this.callee).append("(");
		// If the method is not static, put this in the argument of all function that represents a basic blocks.
		if(!isStatic) {
			sb.append(THIS_PARAM);
			sb.append(", ");
		}

		// Add method parameters
		sb.append(String.join(", ", paramNamesOfMethod));
		if (paramNamesOfMethod.size() > 0) {
			sb.append(", ");
		}

		this.doInterleaved(arguments.stream(), sb, ImpExpr::printOn, b -> b.append(", "));
		sb.append(")");
	}

	@Override
	public void printAt(int level, StringBuilder b) {
		printOn(b);
	}
}
