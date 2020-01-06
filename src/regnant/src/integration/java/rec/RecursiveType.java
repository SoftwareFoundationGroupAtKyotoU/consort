package rec;

import annotation.SkipTest;

import java.util.Random;

public class RecursiveType {
  public static class Node {
    public final Node next;
    public final int i;

    public Node(int i, Node next) {
      this.i = i;
      this.next = next;
    }
  }
  
  @SkipTest
  public static void main(String[] args) {
    Node it = null;
    Random r = new Random();
    while(r.nextInt() == 0) {
      int v = r.nextInt();
      if(v > 0) {
        it = new Node(v, it);
      }
    }
    Node n = it;
    while(n != null) {
      assert n.i > 0;
      n = n.next;
    }
  }
}
