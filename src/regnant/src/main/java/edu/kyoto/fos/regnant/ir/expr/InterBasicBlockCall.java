package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.cfg.BasicBlock;
import soot.Body;

import java.util.stream.Collectors;

public class InterBasicBlockCall extends Call implements Printable {
	public InterBasicBlockCall(Body b, BasicBlock bb) {
		// TODO: データフロー解析の結果（全体）を第二引数に渡す
		super(b.getMethod().getName() + bb.getId(),
				b.getLocals().stream().map(
						local -> new Variable(local.getName(), false)
				).collect(Collectors.toList())
		);
	}

	public InterBasicBlockCall(Body b, String suffix) {
		// TODO: 渡す引数どうするか考える
		super(b.getMethod().getName() + suffix,
				b.getLocals().stream().map(
						local -> new Variable(local.getName(), false)
				).collect(Collectors.toList())
		);
	}

	@Override
	public void printAt(int level, StringBuilder b) {
		super.printOn(b);
	}
}
