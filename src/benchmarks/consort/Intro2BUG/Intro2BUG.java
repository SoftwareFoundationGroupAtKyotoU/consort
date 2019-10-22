import java.util.Random;

public class Intro2BUG {
	static Random r = new Random(42);
	public static class Int {
		int i;
		public Int(int a) {
			this.i = a;
		}
	}

	public static void loop(Int a, Int b) {
		int a_ = a.i;
		b.i += 1;
		a.i += 1;
		assert (a.i == a_ + 1);
		int flg = r.nextInt();
		if(flg < 0) {
			loop(b, new Int(r.nextInt()));
		} else {
			loop(b,b);
		}
	}
		
	public static void main(String[] args) {
		loop(new Int(r.nextInt()), new Int(r.nextInt()));
	}
}
