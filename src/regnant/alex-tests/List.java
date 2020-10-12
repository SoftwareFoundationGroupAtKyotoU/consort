class Node {
    public Node next = null;
    public int value = 42;
}

public class List {
    public Node root = null;
    public void insert(int v) {
        if (root == null) {
            this.root = new Node();
            this.root.value = v;
        } else {
            Node prev = root;
            while (prev.next != null)
                prev = prev.next;
            prev.next = new Node();
            prev.next.value = v;
        }
    }
    public void print() {
        Node n = root;
        while (n != null) {
            System.out.println(n.value);
            n = n.next;
        }
    }
    public static void main(String[] args) {
        List l = new List();
        l.insert(1);
        l.insert(2);
        l.print();
    }
}
