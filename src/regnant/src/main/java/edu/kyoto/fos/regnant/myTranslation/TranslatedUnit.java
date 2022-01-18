package edu.kyoto.fos.regnant.myTranslation;

import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.List;
import java.util.stream.Collectors;

// 変換後の Unit (Stmt) を表すインターフェース
public interface TranslatedUnit {
	// 次の命令が逐次に実行されるかどうか (命令の返り値が unit (void) かどうか, 命令の末尾に 「;」 が来るなら true, 「in」 が来るなら false)
	boolean isSequencing();

	// 変換後の Stmt が ConSORT プログラムに反映されるかどうか (されなかったら true)
	boolean istTranslatedUnitEmpty();

	// Regnant における抽象構文木から ConSORT プログラムに変換するメソッド
	String print(List<String> arguments);

	// インデントをつけて変換後の Unit を出力するメソッド
	default String printWithIndent(int indentLevel, List<String> arguments) {
		StringBuilder builder = new StringBuilder();
		builder.append("  ".repeat(Math.max(0, indentLevel)));
		builder.append(print(arguments));

		return builder.toString();
	}

	// 基本ブロックの呼び出しを関数呼び出しに変換するメソッド
	default String toFunctionCall(BasicBlock basicBlock, List<String> arguments, String funcName) {
		String parametersString = arguments.stream().collect(Collectors.joining(", "));

		StringBuilder builder = new StringBuilder();
		builder
				.append(funcName)
				.append("_")
				.append(basicBlock.id)
				.append("(")
				.append(parametersString)
				.append(")");

		return builder.toString();
	}
}
