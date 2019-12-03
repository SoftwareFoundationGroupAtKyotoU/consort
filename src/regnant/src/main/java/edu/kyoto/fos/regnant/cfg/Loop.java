package edu.kyoto.fos.regnant.cfg;

import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

public class Loop {
  private final BasicBlock header;
  private final HashSet<BasicBlock> all;
  private Collection<BasicBlock> body;

  public Loop(final BasicBlock header, final Set<BasicBlock> body) {
    this.header = header;
    this.all = new HashSet<>(body);
    this.all.add(header);
    this.body = body;
  }

  public Collection<BasicBlock> body() {
    return body;
  }

  public Collection<BasicBlock> all() {
    return all;
  }

  public BasicBlock getHeader() {
    return header;
  }

  @Override public boolean equals(final Object o) {
    if(this == o)
      return true;
    if(o == null || getClass() != o.getClass())
      return false;
    final Loop loop = (Loop) o;
    return Objects.equals(header, loop.header) && Objects.equals(body, loop.body);
  }

  @Override public int hashCode() {
    return Objects.hash(header, body);
  }

  @Override public String toString() {
    return header.toString();
  }
}
