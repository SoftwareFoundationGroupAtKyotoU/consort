public class ObjectFields {
	public static int complexLoop(int a) {
		int toReturn = 0;
		for(int i = 0; i < a || i < 5; i++) {
			toReturn += 2;
		}
		toReturn += 1;
		return toReturn;
	}
	
	public static void main(String[] args) {
		
	}
}
