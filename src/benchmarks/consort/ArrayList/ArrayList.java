import java.util.Random;

public class ArrayList {
	public int[] arr;
	public int len, curr;
	
	public static void copyArray(int i, int[] a, int[] b) {
		if(i == a.length) {
			return;
		}
		b[i] = a[i];
		copyArray(i + 1, a, b);
	}

	private void grow() {
		int newLen = (this.len * 2) + 1;
		int[] newArr = new int[newLen];;
		copyArray(0, this.arr, newArr);
		this.len = newLen;
		this.arr = newArr;
	}

	public void push(int i) {
		if(this.curr == this.len) {
			this.grow();
		}
		assert this.curr > 0;
		assert this.curr < this.arr.length;
		this.arr[curr] = i;
		this.curr++;
	}

	public static void pushLoop(Random r, ArrayList l) {
		int i = r.nextInt();
		l.push(i);
		pushLoop(r, l);
	}

	public ArrayList(int sz) {
		this.len = sz;
		this.curr = 0;
		this.arr = new int[sz];
	}
	
	public static void main(String[] args) {
		Random r = new Random(42);
		int i = r.nextInt();
		if(i < 0) {
			return;
		}
		pushLoop(r, new ArrayList(i));
	}
}
