package edu.kyoto.fos.regnant.cfg;

import soot.Unit;
import soot.toolkits.graph.DirectedGraph;

import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

// 基本ブロック単位での制御フローグラフのメソッドを提供するクラス
public class BasicBlockGraph implements DirectedGraph<BasicBlock> {
  private final DirectedGraph<Unit> ug;
  private final BasicBlockMapper bbm;

  public BasicBlockGraph(DirectedGraph<Unit> ug, BasicBlockMapper bbm) {
    this.ug = ug;
    this.bbm = bbm;
  }


  @Override public List<BasicBlock> getHeads() {
    return ug.getHeads().stream().map(bbm::getBlockByHead).collect(Collectors.toList());
  }

  @Override public List<BasicBlock> getTails() {
    return ug.getHeads().stream().map(bbm::getBlockByTail).collect(Collectors.toList());
  }

  @Override public List<BasicBlock> getPredsOf(final BasicBlock s) {
    Unit hd = s.getHead();
    return ug.getPredsOf(hd).stream()
        .map(u -> {
          if(u.hasTag(RevMapTag.REV_MAP)) {
            return ((RevMapTag)u.getTag(RevMapTag.REV_MAP)).unit;
          } else {
            return u;
          }
        })
        .map(bbm::getBlockByTail).collect(Collectors.toList());
  }

  @Override public List<BasicBlock> getSuccsOf(final BasicBlock s) {
    Unit tl = s.getTail();
    return ug.getSuccsOf(tl).stream()
        .map(u -> {
          if(u.hasTag(RemapTag.REMAP)) {
            return ((RemapTag)u.getTag(RemapTag.REMAP)).target;
          } else {
            return u;
          }
        }).map(bbm::getBlockByHead).collect(Collectors.toList());
  }

  @Override public int size() {
    return this.bbm.size();
  }

  @Override public Iterator<BasicBlock> iterator() {
    return bbm.iterator();
  }
}
