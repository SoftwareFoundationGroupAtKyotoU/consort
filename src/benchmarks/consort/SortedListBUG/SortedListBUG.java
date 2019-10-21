import java.util.Random;

public class SortedListBUG {
	public static class Node {
		int data;
		Node next;
		public Node(int data, Node next) {
			this.data = data;
			this.next = next;
		}
		public void insert(int i) {
			if(this.data > i) {
				if(this.next == null) {
					this.next = new Node(i, null);
				} else {
					this.next.insert(i);
				}
			} else {
				int val = this.data;
				this.data = i;
				this.next = new Node(val, this.next);
			}
		}

		public void assertSorted() {
			if(this.next != null) {
				int nextVal = this.next.data;
				assert this.data <= nextVal;
				this.next.assertSorted();
			}
		}
	}
	
	public static class List {
		Node hd;
		public static List make() {
			return new List();
		}

		public void insert(int i) {
			if(this.hd == null) {
				this.hd = new Node(i, null);
			} else {
				this.hd.insert(i);
			}
		}

		public void assertSorted() {
			if(this.hd != null) {
				this.hd.assertSorted();
			}
		}
	}

	public static void main(String[] args) {
		List i = List.make();
		Random r = new Random(42);
		while(r.nextInt() > 0) {
			i.insert(r.nextInt());
		}
		i.assertSorted();
	}
}
