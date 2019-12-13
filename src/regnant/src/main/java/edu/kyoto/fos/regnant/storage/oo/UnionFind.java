package edu.kyoto.fos.regnant.storage.oo;

import java.util.HashMap;
import java.util.stream.Stream;

public class UnionFind<N> {
  public Stream<N> universe() {
    return universe.keySet().stream();
  }

  public class Node {
    Node parent = this;
    int rank = 0;
    N data;
    Node(N data) {
      this.data = data;
    }

    public N getData() {
      return this.data;
    }
  }

  private HashMap<N, Node> universe = new HashMap<>();

  private Node get(N x) {
    return universe.computeIfAbsent(x, Node::new);
  }

  private Node find(final Node node) {
    Node it = node;
    while(it.parent != it) {
      it.parent = it.parent.parent;
      it = it.parent;
    }
    return it;
  }

  public Node find(N n) {
    return find(get(n));
  }

  public Node union(final Node n1, final Node n2) {
    Node xRoot = find(n1);
    Node yRoot = find(n2);
    if(xRoot == yRoot) {
      return xRoot;
    }
    if(xRoot.rank < yRoot.rank) {
      Node t = xRoot;
      xRoot = yRoot;
      yRoot = t;
    }
    yRoot.parent = xRoot;
    if(xRoot.rank == yRoot.rank) {
      xRoot.rank += 1;
    }
    return xRoot;
  }
}
