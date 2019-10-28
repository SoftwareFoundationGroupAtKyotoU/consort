public class ShuffleBUG {
	int i;
	public ShuffleBUG(int i) {
		this.i = i;
	}
	public static void main(String[] args) {
		ShuffleBUG x = new ShuffleBUG(1);
		ShuffleBUG y = x;
		x.i = x.i + 1;
		if(x != y) {
			return;
		}
		y.i = y.i + 1;
		if(x != y) {
			return;
		}
		x.i = x.i + 1;
		if(x != y) {
			return;
		}
		assert y.i == 5;
	}
}
