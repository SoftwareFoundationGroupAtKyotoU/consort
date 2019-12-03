package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.Printable;
import edu.kyoto.fos.regnant.cfg.BasicBlock;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class GraphElem implements Targeted, Printable {
  protected boolean isLoop;

  protected GraphElem(boolean isLoop) {
    this.isLoop = isLoop;
  }

  protected GraphElem() {
    this.isLoop = false;
  }

  public abstract BasicBlock getHead();
  public List<BasicBlock> heads() {
    return Collections.singletonList(this.getHead());
  }

  public String dump() {
    StringBuilder sb = new StringBuilder();
    this.printAt(0, sb);
    return sb.toString();
  }

  protected StringBuilder indentAndLoop(final int i, final StringBuilder sb) {
    indent(i, sb);
    if(isLoop) {
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

  public boolean isLoop() {
    return isLoop;
  }

  public void setLoopHeader(final boolean isLoopHeader) {
    this.isLoop = isLoopHeader;
  }
}
