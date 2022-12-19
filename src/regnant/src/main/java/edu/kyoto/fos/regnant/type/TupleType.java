package edu.kyoto.fos.regnant.type;

import java.util.List;
import java.util.stream.Collectors;

public class TupleType implements RegnantType {
	private final List<RegnantType> typeOfContents;

	public TupleType(List<RegnantType> typeOfContents) {
		this.typeOfContents = typeOfContents;
	}

	public String InitialValue() {
		return "(" +
				typeOfContents.stream().map(RegnantType::InitialValue).collect(Collectors.joining(", ")) +
				")";
	}
}
