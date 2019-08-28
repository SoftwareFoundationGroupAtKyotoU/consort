public class Null {
	public static class Ptr {
		int a;
	}

	public static Ptr get() {
		return null;
	}

	public static void main(String[] args) {
		Ptr p = get();
		System.out.println(p.a);
	}
}
