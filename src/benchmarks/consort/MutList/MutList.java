import java.util.Random;

public class MutList {
	public static class Node {
		int data;
		Node next;
		public Node(int data, Node next) {
			this.data = data;
			this.next = next;
		}

		public void allPositive() {
			assert this.data > 0;
			if(this.next != null) {
				this.next.allPositive();
			}
		}
	}
	
	public static class List {
		Node hd;
		public static List make() {
			return new List();
		}

		public void add(int i) {
			this.hd = new Node(i, this.hd);
		}

		public void clear() {
			this.hd = null;
		}
		public void allPositive() {
			if(this.hd == null) {
				return;
			}
			this.hd.allPositive();
		}
	}

	public static void main(String[] args) {
		List l1 = new List();//List.make();
		List l3 = l1;
		List l2 = new List();//List.make();
		Random r = new Random(42);
		int pos = r.nextInt();
		if(pos <= 0) {
			return;
		}
		l1.add(pos);
		pos = r.nextInt();
		if(pos <= 0) {
			return;
		}
		l1.add(pos);
		// alias assertion 1
		if(l3 != l1) {
			return;
		}
		pos = r.nextInt();
		if(pos <= 0) {
			return;
		}
		l3.add(pos);
		// alias assertion 2
		if(l3 != l1) {
			return;
		}
		l2.add(-4);
		l2.clear();
		pos = r.nextInt();
		if(pos <= 0) {
			return;
		}
		l2.add(pos);
		l1.allPositive();
		l2.allPositive();
	}
}
