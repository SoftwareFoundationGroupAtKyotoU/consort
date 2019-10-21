public class Shuffle {
	int i;
	public Shuffle(int i) {
		this.i = i;
	}
	public static void main(String[] args) {
		Shuffle x = new Shuffle(1);
		Shuffle y = x;
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
		assert y.i == 4;
	}
}
