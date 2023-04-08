package edu.kyoto.fos.regnant.cfg;

import soot.Body;
import soot.toolkits.graph.BriefUnitGraph;

public class CFGReconstructor {
  private final BasicBlockMapper bbm;
  private BasicBlockGraph bbg;

  public CFGReconstructor(Body b) {
    this.bbm = new BasicBlockMapper(b);
    this.bbg = new BasicBlockGraph(new BriefUnitGraph(b), bbm);
  }

  public BasicBlockMapper GetBasicBlockMapper() {
    return bbm;
  }

  public BasicBlockGraph GetBasicBlockGraph() {
    return bbg;
  }

  public String dump() {
    // TODO: dumpを実装する
    return "";
  }
}