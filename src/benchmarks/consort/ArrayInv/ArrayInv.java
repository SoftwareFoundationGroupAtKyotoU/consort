public class ArrayInv {
	public static void main(String[] args) {
		int[] a = new int[7];
		for(int i = 0; i < a.length; i++) {
			a[i] = i;
		}
		for(int i = 0; i < a.length; i++) {
			assert a[i] == i;
		}
	}
}
