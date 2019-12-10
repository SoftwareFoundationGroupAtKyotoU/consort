package edu.kyoto.fos.regnant.translation;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class UnreachableTag implements Tag {

  public static final String NAME = "RegnantUnreachable";

  @Override public String getName() {
    return NAME;
  }

  @Override public byte[] getValue() throws AttributeValueException {
    return new byte[0];
  }
}
