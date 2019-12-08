package edu.kyoto.fos.regnant.cfg;

import soot.Unit;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class RevMapTag implements Tag {
  public static final String REV_MAP = "RevMapTag";
  public final Unit unit;

  public RevMapTag(final Unit unit) {
    this.unit = unit;
  }

  @Override public String getName() {
    return REV_MAP;
  }

  @Override public byte[] getValue() throws AttributeValueException {
    throw new RuntimeException();
  }

  @Override public String toString() {
    return "(" + REV_MAP + "=>" + this.unit +")";
  }
}
