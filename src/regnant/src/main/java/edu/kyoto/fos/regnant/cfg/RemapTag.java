package edu.kyoto.fos.regnant.cfg;

import soot.Unit;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class RemapTag implements Tag {
  public static final String REMAP = "Remapping";
  public final Unit target;
  public RemapTag(final Unit target) {
    this.target = target;
  }

  @Override public String getName() {
    return REMAP;
  }

  @Override public byte[] getValue() throws AttributeValueException {
    throw new RuntimeException("No bytecode repr");
  }

  @Override public String toString() {
    return "(" + REMAP + " => " + this.target + ")";
  }
}
