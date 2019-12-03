package edu.kyoto.fos.regnant.cfg.graph;

import edu.kyoto.fos.regnant.Printable;

import java.util.Optional;

public abstract class Continuation implements Targeted, Printable, TerminalNode {
  public abstract Optional<GraphElem> elem();
}
