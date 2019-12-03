package edu.kyoto.fos.regnant.cfg;

import soot.toolkits.graph.DominatorTree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class BlockTree<N> {
  public List<N> nodes = new ArrayList<>();
  public Map<N, List<N>> children = new HashMap<>();
  public Map<N, N> parent = new HashMap<>();
  public Map<N, Integer> level = new HashMap<>();

  public BlockTree(DominatorTree<N> seed) {
    seed.forEach(i -> {
      nodes.add(i.getGode());
      children.put(i.getGode(), new ArrayList<>());
    });
    seed.forEach(i -> {
      seed.getChildrenOf(i).forEach(c -> {
        children.get(i.getGode()).add(c.getGode());
        parent.put(c.getGode(), i.getGode());
      });
    });
    assignLevels();
  }

  private void assignLevels() {
    nodes.stream().filter(p -> !parent.containsKey(p)).forEach(p -> assignLevel(p, 0));
  }

  private void assignLevel(final N p, final int i) {
    level.put(p, i);
    children.get(p).forEach(c -> assignLevel(c, i + 1));
  }

  public void shiftTo(N node, N newParent) {
    int lvl = level.get(newParent);
    N currParent = parent.get(node);
    assert currParent != null;
    children.get(currParent).remove(node);
    children.get(newParent).add(node);
    parent.put(node, newParent);
    assignLevel(node, lvl + 1);
  }
}
