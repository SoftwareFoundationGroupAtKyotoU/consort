package edu.kyoto.fos.regnant.storage.oo;

import java.util.HashMap;
import java.util.stream.Stream;

public class UnionFind<N> {
  public Stream<N> universe() {
    return universe.keySet().stream();
  }

  public static class Node<U> {
    Node<U> parent = this;
    int rank = 0;
    U data;
    Node(U data) {
      this.data = data;
    }

    public U getData() {
      return this.data;
    }
  }

  private HashMap<N, Node<N>> universe = new HashMap<>();

  private Node<N> get(N x) {
    return universe.computeIfAbsent(x, Node::new);
  }

  private Node<N> find(final Node<N> node) {
    var it = node;
    while(it.parent != it) {
      it.parent = it.parent.parent;
      it = it.parent;
    }
    return it;
  }

  public Node<N> find(N n) {
    return find(get(n));
  }

  public Node<N> union(final Node<N> n1, final Node<N> n2) {
    var xRoot = find(n1);
    var yRoot = find(n2);
    if(xRoot == yRoot) {
      return xRoot;
    }
    if(xRoot.rank < yRoot.rank) {
      var t = xRoot;
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
