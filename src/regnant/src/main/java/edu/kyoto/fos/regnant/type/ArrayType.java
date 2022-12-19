package edu.kyoto.fos.regnant.type;

public class ArrayType implements RegnantType{

	public ArrayType(int size) {
	}

	public String InitialValue() {
		return "mkarray 0";
	}
}
