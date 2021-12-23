package edu.kyoto.fos.regnant.cfg;

import soot.Body;
import soot.Unit;
import soot.jimple.GotoStmt;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

// 基本ブロックを表すクラス
public class BasicBlockMapper {
  // hdMap は基本ブロックのはじめの Unit、基本ブロック全体の Map
  // tlMap は基本ブロックの終わりの Unit、基本ブロック全体の Map
  private Map<Unit, BasicBlock> hdMap = new HashMap<>();
  private Map<Unit, BasicBlock> tlMap = new HashMap<>();

  public BasicBlockMapper(final Body b) {
    HashSet<Unit> start = new HashSet<>();
    BriefUnitGraph ug = new BriefUnitGraph(b);
    // start に直前に Unit が2つ以上ある Unit を入れる
    for(Unit u : b.getUnits()) {
      if(ug.getPredsOf(u).size() > 1) {
        start.add(u);
      }
    }
    // はじめの unit を worklist に入れる
    LinkedList<Unit> worklist = new LinkedList<>(ug.getHeads());
    Set<Unit> visited = new HashSet<>();
    List<List<Unit>> blocks = new ArrayList<>();
    // BriefUnitGraph を二股以上になっている部分を全て分割して一列の currChain の集まりにして block に入れる (currChain 間のUnit の重複はなし)
    // 要するに基本ブロックに分けている
    while(!worklist.isEmpty()) {
      List<Unit> currChain = new ArrayList<>();
      Unit u = worklist.pop();
      if(!visited.add(u)) {
        continue;
      }
      assert ug.getHeads().contains(u) || ug.getPredsOf(u).size() > 1 ||
          (ug.getPredsOf(u).size() == 1 && ug.getSuccsOf(ug.getPredsOf(u).get(0)).size() > 1);
      currChain.add(u);
      Unit it = u;
      // グラフが二股以上になった時点でループを抜ける
      while(true) {
        List<Unit> succs = ug.getSuccsOf(it);
        if(succs.size() != 1 || start.contains(succs.get(0))) {
          // terminal
          worklist.addAll(succs);
          break;
        }
        it = succs.get(0);
        currChain.add(it);
      }
      blocks.add(currChain);
    }
    // now, collapse "fall through" blocks
    // Goto 命令だけの場合はそれを消して前の Unit を指す RevMapTag と後の Unit を指す RemapTag を付ける. このタグは BasicBlockGraph の getSuccsOf や getPredsOf に使われる 
    blocks.stream().flatMap(uList -> {
      if(uList.size() == 1) {
        Unit u = uList.get(0);
        if(u instanceof GotoStmt) {
          // collapse
          List<Unit> pred = ug.getPredsOf(u);
          if(pred.size() == 1) {
            u.addTag(new RemapTag(((GotoStmt) u).getTarget()));
            u.addTag(new RevMapTag(pred.get(0)));
            return Stream.empty();
          }
        }
      }
      return Stream.of(uList);
    // 基本ブロックから hdMap と tlMap を作る
    }).map(BasicBlock::new).forEach(bb -> {
      hdMap.put(bb.getHead(), bb);
      tlMap.put(bb.getTail(), bb);
    });
  }

  public int size() {
    return hdMap.size();
  }

  public BasicBlock getBlockByHead(final Unit unit) {
    assert hdMap.containsKey(unit) : unit;
    return hdMap.get(unit);
  }

  public BasicBlock getBlockByTail(final Unit unit) {
    assert tlMap.containsKey(unit) : unit;
    return tlMap.get(unit);
  }

  public Iterator<BasicBlock> iterator() {
    return hdMap.values().iterator();
  }

  // 追加
  public Map<Unit, BasicBlock> getHdMap() {
    return hdMap;
  }
}
