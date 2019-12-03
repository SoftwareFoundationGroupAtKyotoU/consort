package edu.kyoto.fos.regnant.cfg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

public class LoopTree {
  private Map<BasicBlock, Loop> headerMap;
  private Map<Loop, List<Loop>> parentRelation = new HashMap<>();
  private Map<Loop, List<Loop>> childRelation = new HashMap<>();
  private Map<BasicBlock, List<Loop>> containingLoops = new HashMap<>();

  public List<Loop> containingLoops(BasicBlock b) {
    return this.containingLoops.getOrDefault(b, Collections.emptyList());
  }

  public LoopTree(final Map<BasicBlock,Set<BasicBlock>> loopMap) {
    this.headerMap = loopMap.entrySet().stream().collect(Collectors.toMap(Entry::getKey, it ->
      new Loop(it.getKey(), it.getValue())
    ));
    this.headerMap.values().forEach(l -> {
      l.all().forEach(bb -> {
        containingLoops.putIfAbsent(bb, new ArrayList<>());
        containingLoops.get(bb).add(l);
      });
      childRelation.put(l, new ArrayList<>());
      l.body().stream().filter(headerMap::containsKey).map(headerMap::get).forEach(c -> {
        parentRelation.putIfAbsent(c, new ArrayList<>());
        parentRelation.get(c).add(l);
        childRelation.get(l).add(c);
      });
    });
  }

  public boolean isLoopHeader(final BasicBlock head) {
    return headerMap.containsKey(head);
  }
}
