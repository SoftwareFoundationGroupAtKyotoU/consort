package edu.kyoto.fos.regnant.myTranslation;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.myTranslation.Service.TranslateStmtService;
import edu.kyoto.fos.regnant.myTranslation.translatedExpr.IntConst;
import edu.kyoto.fos.regnant.myTranslation.translatedStmt.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

// ConSORT プログラムに変換された基本ブロックを表すためのクラス
public class TranslatedBasicBlock {
	// name は関数名, id は基本ブロックのナンバリング, translatedBasicBlock は変換後の式のリスト, arguments は変換後の元々の関数の引数, bound は変換後の基本ブロックの関数の引数, assigned は変換後の基本ブロックで代入される変数, nextBasicBlocks は次の基本ブロック, gotoFlag は次の基本ブロックを呼び出す必要があるかどうか
	private final String name;
	private final int id;
	private final boolean headOfFunction;
	private List<TranslatedUnit> translatedBasicBlock = new ArrayList<>();
	private final List<String> parameters = new ArrayList<>();
	private final List<String> bound = new ArrayList<>();
	private final List<String> assigned = new ArrayList<>();
	private final List<BasicBlock> nextBasicBlocks;

	public TranslatedBasicBlock(String name, BasicBlock basicBlock, boolean headOfFunction, List<BasicBlock> nextBasicBlocks) {
		TranslateStmtService service = new TranslateStmtService();

		this.name = name;
		this.id = basicBlock.id;
		this.headOfFunction = headOfFunction;
		this.nextBasicBlocks = nextBasicBlocks;

		for (int i = 0; i < basicBlock.units.size(); i++) {
			TranslatedUnit translatedUnit = service.translate(basicBlock.units.get(i), headOfFunction, nextBasicBlocks, name);

			// もし変換後の unit が Argument だった場合, 関数の引数になる変数があるので, それを arguments フィールドに入れる
			if (translatedUnit instanceof Argument) parameters.add(((Argument) translatedUnit).getArgumentVariable());
			// もし変換後の unit が NewVariable か NewPrimitiveVariable だった場合, 基本ブロックの引数になる変数があるので, それを bound フィールドに入れる
			if (translatedUnit instanceof NewRef) bound.add(((NewRef) translatedUnit).getBoundVariable());
			if (translatedUnit instanceof NewPrimitiveVariable)
				bound.add(((NewPrimitiveVariable) translatedUnit).getBoundVariable());
			// もし変換後の unit が AssignToVariable だった場合, 最初の基本ブロックにない変数定義になりうる
			if (translatedUnit instanceof AssignToVariable)
				assigned.add(((AssignToVariable) translatedUnit).getAssignedVariable());

			translatedBasicBlock.add(translatedUnit);

			// assert は必ず失敗するようにしているので assert の先の命令を無視して return 文に変換するs
			if (translatedUnit instanceof AssertFail) {
				translatedBasicBlock.add(new ReturnVoid());
				break;
			}
		}
	}

	// arguments を返すメソッド
	public List<String> getParameters() {
		return parameters;
	}

	// bound を返すメソッド
	public List<String> getBound() {
		return bound;
	}

	// assigned を返すメソッド
	public List<String> getAssigned() {
		return assigned;
	}

	// 波括弧の左側を付けるためのメソッド
	private String printLeftBraces(int indentLevel) {
		StringBuilder builder = new StringBuilder();
		builder.append("  ".repeat(Math.max(0, indentLevel)));
		builder.append("{");

		return builder.toString();
	}

	// 波括弧の右側を付けるためのメソッド
	private String printRightBraces(int indentLevel) {
		StringBuilder builder = new StringBuilder();

		// 波括弧の右側は必ず基本ブロックの最後にくるのでインデントの個数から付ける波括弧の個数を判別する
		for (int i = indentLevel; i > 0; i--) {
			builder.append("  ".repeat(i));
			builder.append("}\n");
		}

		return builder.toString();
	}

	// 基本ブロックの最後の Unit を得るメソッド
	private TranslatedUnit getTail() {
		return translatedBasicBlock.get(translatedBasicBlock.size() - 1);
	}

	// 基本ブロックを関数名と関数呼び出し付きで出力するメソッド
	public String print(List<String> allArguments, List<String> allBound, List<String> allUndefined, HashMap<String, Integer> headIDs) {

		// 引数のための, allArguments と allBound, allUndefined を合わせたリスト
		List<String> restArguments = Stream.concat(Stream.concat(allArguments.stream(), allBound.stream()), allUndefined.stream())
				.collect(Collectors.toList());

		// 引数部分の作成. 初めの基本ブロックはパラメータのみ, 以降の基本ブロックはパラメータと宣言された変数を引数にとる
		String parametersString = (headOfFunction ? allArguments : restArguments).stream().collect(Collectors.joining(", "));

		// 関数の中身の作成. ただし右の波括弧は末尾の関数呼び出しの後に入れたいので最後に回している
		boolean prevSequence = true;
		int indentLevel = 1;
		StringBuilder basicBlocksBuilder = new StringBuilder();
		for (TranslatedUnit translatedUnit : translatedBasicBlock) {
			if (!translatedUnit.istTranslatedUnitEmpty()) {
				if (translatedUnit.isSequencing() && !prevSequence) {
					indentLevel++;

					basicBlocksBuilder
							.append(printLeftBraces(indentLevel - 1))
							.append("\n")
							.append(translatedUnit.printWithIndent(indentLevel, restArguments, headIDs))
							.append("\n");
				} else {
					basicBlocksBuilder
							.append(translatedUnit.printWithIndent(indentLevel, restArguments, headIDs))
							.append("\n");
				}
			}

			prevSequence = translatedUnit.isSequencing();
		}

		String basicBlocksString = basicBlocksBuilder.toString();

		// 次の基本ブロックを呼び出す部分の作成
		StringBuilder nextBasicBlockBuilder = new StringBuilder();

		// 次の基本ブロックの引数部分の作成
		String callArgumentsString = restArguments.stream().collect(Collectors.joining(", "));

		if (!(getTail() instanceof If || getTail() instanceof Goto || getTail() instanceof ReturnVoid || nextBasicBlocks.size() == 0)) {
			nextBasicBlockBuilder.append("  ".repeat(Math.max(0, indentLevel)));

			assert (nextBasicBlocks.size() == 1);

			nextBasicBlockBuilder
					.append(name)
					.append("_")
					.append(nextBasicBlocks.get(0).id)
					.append("(")
					.append(callArgumentsString)
					.append(")\n");
		}

		String nextBasicBlock = nextBasicBlockBuilder.toString();

		// 結合
		StringBuilder builder = new StringBuilder();
		builder
				.append(name)
				.append("_")
				.append(id)
				.append("(")
				.append(parametersString)
				.append(") { \n")
				.append(basicBlocksString)
				.append(nextBasicBlock)
				.append(printRightBraces(indentLevel - 1))
				.append("}\n");

		return builder.toString();
	}

	// 最初の基本ブロック以外で変数が定義された場合に使う、変数定義を追加するためのメソッド (最初の基本ブロック用)
	public void addDefines(List<String> allUndefined) {
		assert (headOfFunction);

		translatedBasicBlock = Stream.concat(allUndefined.stream().map(v -> new NewRef(v, new IntConst("0"))), translatedBasicBlock.stream())
				.collect(Collectors.toList());
	}
}
