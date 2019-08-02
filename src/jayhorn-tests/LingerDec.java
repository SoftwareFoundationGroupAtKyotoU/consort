class LingerDec {
	public static class Ptr {
		public int a;
	}

	public static boolean linger_dec(Ptr ma) {
		ma.a = -1;
		if(Havoc_Class.havoc_int() == 0) {
			return true;
		} else {
			int b = Havoc_Class.havoc_int();
			if(b > 0) {
				int old_b = b;
				Ptr mb = new Ptr();
				mb.a = b;
				boolean res;
				if(Havoc_Class.havoc_int() == 0) {
					res = linger_dec(ma);
				} else {
					res = linger_dec(mb);
				}
				//boolean res = linger_dec(Havoc_Class.havoc_int() == 0 ? ma : mb);
				return res && old_b >= mb.a;
			} else {
				return linger_dec(ma);
			}
		}
	}
	
	public static void main(String[] args) {
		Ptr p = new Ptr();
		int b = Havoc_Class.havoc_int();
		if(b > 0) {
			p.a = b;
			assert linger_dec(p);
		}
	}
}
