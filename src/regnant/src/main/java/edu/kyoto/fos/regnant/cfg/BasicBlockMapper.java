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

public class BasicBlockMapper {
  private Map<Unit, BasicBlock> hdMap = new HashMap<>();
  private Map<Unit, BasicBlock> tlMap = new HashMap<>();

  public BasicBlockMapper(final Body b) {
    HashSet<Unit> start = new HashSet<>();
    BriefUnitGraph ug = new BriefUnitGraph(b);
    for(Unit u : b.getUnits()) {
      if(ug.getPredsOf(u).size() > 1) {
        start.add(u);
      }
    }
    LinkedList<Unit> worklist = new LinkedList<>(ug.getHeads());
    Set<Unit> visited = new HashSet<>();
    List<List<Unit>> blocks = new ArrayList<>();
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
}
