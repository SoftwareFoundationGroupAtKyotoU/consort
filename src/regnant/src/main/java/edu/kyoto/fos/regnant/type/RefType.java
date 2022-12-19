package edu.kyoto.fos.regnant.type;

public class RefType implements RegnantType{
	// Type of the variable pointing to
	private final RegnantType typePointsTo;

	public RefType(RegnantType typePointsTo) {
		this.typePointsTo = typePointsTo;
	}

	public String InitialValue() {
		return "mkref " + typePointsTo.InitialValue();
	}
}
