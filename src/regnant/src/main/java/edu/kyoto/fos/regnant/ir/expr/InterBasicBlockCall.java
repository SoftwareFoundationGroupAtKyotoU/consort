package edu.kyoto.fos.regnant.ir.expr;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.cfg.BasicBlockMapper;
import soot.Body;
import soot.Unit;

import java.util.stream.Collectors;

public class InterBasicBlockCall extends Call implements Printable {
	public InterBasicBlockCall(Body b, BasicBlockMapper bbm, Unit calleeHeadUnit) {
		// TODO: データフロー解析の結果（全体）を第二引数に渡す
		super(b.getMethod().getName() + bbm.getBlockByHead(calleeHeadUnit).getId(),
				b.getLocals().stream().map(
						local -> new Variable(local.getName(), false)
				).collect(Collectors.toList())
		);
	}

	@Override
	public void printAt(int level, StringBuilder b) {
		//TODO: ここ何を書けばいいか考える（書く必要ある？）
	}
}
