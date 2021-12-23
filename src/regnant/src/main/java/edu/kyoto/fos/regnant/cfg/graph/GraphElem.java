package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class GraphElem implements Targeted, Printable {
  protected GraphElem() {
  }

  public abstract BasicBlock getHead();
  public List<BasicBlock> heads() {
    return Collections.singletonList(this.getHead());
  }

  // 基本ブロックの制御フローグラフを出力するメソッド (現行 regnant 向けの形、break の変換の仕方が良くない)
  public String dump() {
    StringBuilder sb = new StringBuilder();
    this.printAt(0, sb);
    return sb.toString();
  }

  public boolean isLoop() {
    return false;
  }

  protected StringBuilder indentAndLoop(final int i, final StringBuilder sb) {
    indent(i, sb);
    if(isLoop()) {
      sb.append("loop: ");
    }
    return sb;
  }

  private Map<String, Object> annot = new HashMap<>();
  public Map<String, Object> getAnnot() {
    return annot;
  }

  public <T> T getAnnotation(String s, Class<T> klass) {
    Object o = annot.get(s);
    if(o == null) {
      return null;
    }
    return klass.cast(o);
  }

  public void putAnnotation(String s, Object o) {
    this.annot.put(s, o);
  }
}
