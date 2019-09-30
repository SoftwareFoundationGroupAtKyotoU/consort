class FalseNegative {
	public static class Ptr {
		public int a;
	}

	public static void neg(Ptr p) {
		p.a = -p.a;
	}

	public static void rec(Ptr p, boolean b) {
		if(b) {
			neg(p);
			p.a++;
		} else {
			neg(p);
			rec(p, true);
		}
	}
	
	public static void main(String[] args) {
		Ptr p = new Ptr();
		p.a = Havoc_Class.havoc_int();
		int d = p.a;
		rec(p, false);
		assert d != p.a;
	}
}
