class Trivial {
	public static class Ptr {
		public int a;
	}
	
	public static void main(String[] args) {
		Ptr p = new Ptr();
		p.a = Havoc_Class.havoc_int();
		int d = p.a;
		p.a += 1;
		assert d < p.a;
	}
}
