package edu.kyoto.fos.regnant.myTranslation;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.cfg.CFGReconstructor;
import edu.kyoto.fos.regnant.myTranslation.translatedStmt.AssignToVariable;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

// TODO: 環境 (初出の変数がどれか) を関数ごとに作るように変更する
// TODO: 無駄な Unit を減らす (関数呼び出しの後の Unit とか)
// TODO: 無駄な基本ブロックを減らす (return 文だけの基本ブロックが大量に生成される. もしかしたら検証器には嬉しかったりするのか？)
// TODO: オブジェクト指向の部分を big tuple で命令型言語に置き換えるようにする (もしかしたら CFGReconstructor の時点でできているのかも)
// TODO: alias 文を自動で挿入するようにする
// TODO: もしかしたら関数の返り値を伝える必要があるかも
// TODO: GotoStmt は基本ブロックとして分けないようにする

// ConSORT プログラムに変換された関数を表すクラス
public class TranslatedFunction {
	// translatedFunction は変換後の関数, allArguments はメソッドの引数のリスト, allBound は宣言された変数のリストを表す
	private final List<TranslatedBasicBlock> translatedFunction = new ArrayList<>();
	private List<String> allParameters = new ArrayList<>();
	private List<String> allBound = new ArrayList<>();
	private final List<String> allUndefined = new ArrayList<>();

	public TranslatedFunction(CFGReconstructor cfg) {
		// 基本ブロックを出力
		System.out.println(cfg.dump());

		int head = 0;
		List<String> headEnv = new ArrayList<>();
		List<String> allAssigned = new ArrayList<>();
		List<BasicBlock> basicBlocks = new ArrayList<>(cfg.getBbm().getHdMap().values());
		for (int i = 0; i < basicBlocks.size(); i++) {
			List<BasicBlock> nextBasicBlocks = cfg.getBbg().getSuccsOf(basicBlocks.get(i));

			if (cfg.getBbg().getHeads().contains(basicBlocks.get(i))) {
				// 関数のはじめの基本ブロックだけ headOfFunction を true にし, arguments を TranslatedFunction に返す
				TranslatedBasicBlock headBasicBlock = new TranslatedBasicBlock(basicBlocks.get(i), true, nextBasicBlocks);
				this.translatedFunction.add(headBasicBlock);
				this.allParameters = Stream.concat(allParameters.stream(), headBasicBlock.getParameters().stream())
						.collect(Collectors.toList());
				this.allBound = Stream.concat(allBound.stream(), headBasicBlock.getBound().stream())
						.collect(Collectors.toList());

				// headEnv は関数の最初の基本ブロックで定義されている変数
				headEnv = Stream.concat(headBasicBlock.getParameters().stream(), headBasicBlock.getBound().stream())
						.collect(Collectors.toList());

				// head は関数の最初の基本ブロックのインデックス
				head = i;
			} else {
				// 返ってきた arguments を他の基本ブロックに渡す
				TranslatedBasicBlock basicBlock = new TranslatedBasicBlock(basicBlocks.get(i), false, nextBasicBlocks);
				this.translatedFunction.add(basicBlock);
				this.allParameters = Stream.concat(allParameters.stream(), basicBlock.getParameters().stream())
						.collect(Collectors.toList());
				this.allBound = Stream.concat(allBound.stream(), basicBlock.getBound().stream())
						.collect(Collectors.toList());

				// allAssigned は最初の基本ブロック以外で代入されている変数
				allAssigned = Stream.concat(allAssigned.stream(), basicBlock.getAssigned().stream())
						.collect(Collectors.toList());
			}
		}

		// 代入された変数が最初の基本ブロックで定義されていなければ allUndefined に加える
		for (String variable : allAssigned) {
			if (!(headEnv.contains(variable) || this.allUndefined.contains(variable))) {
				this.allUndefined.add(variable);
			}
		}

		translatedFunction.get(head).addDefines(this.allUndefined);
	}

	// 変換後の関数をファイルに書き込むためのメソッド
	public void print(String path) {
		// 変換後の関数を文字列にする
		String functionString = translatedFunction.stream().map(bb -> bb.print(allParameters, allBound, allUndefined)).collect(Collectors.joining("\n"));

		try (PrintWriter pw = new PrintWriter(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(path, true), StandardCharsets.UTF_8)))) {
			// ファイルへの書き込み
			pw.println(functionString);
		} catch (IOException ex) {
			System.err.println(ex);
		}
	}
}
