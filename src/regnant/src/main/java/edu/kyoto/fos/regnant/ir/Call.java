package edu.kyoto.fos.regnant.ir;

import soot.Local;

import java.util.List;
import java.util.stream.Collectors;

public class Call extends Effect {
  private final String name;
  private final List<Local> args;

  public Call(final String name, final List<Local> args) {
    this.name = name;
    this.args = args;
  }

  @Override public void printAt(final int level, final StringBuilder b) {
    indent(level, b).append(name);
    b.append(args.stream().map(Local::getName).collect(Collectors.joining(", ", "(", ")")));
  }
}
