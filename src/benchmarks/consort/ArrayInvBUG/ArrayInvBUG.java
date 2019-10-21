public class ArrayInvBUG {
	public static void main(String[] args) {
		int[] a = new int[7];
		for(int i = 0; i < a.length; i++) {
			a[i] = i;
		}
		a[6] = 0;
		for(int i = 0; i < a.length; i++) {
			assert a[i] == i;
		}
	}
}
