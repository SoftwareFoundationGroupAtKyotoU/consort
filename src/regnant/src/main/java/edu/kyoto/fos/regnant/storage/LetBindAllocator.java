package edu.kyoto.fos.regnant.storage;

import edu.kyoto.fos.regnant.cfg.BasicBlock;
import edu.kyoto.fos.regnant.cfg.BlockTree;
import fj.P;
import fj.P2;
import soot.Local;
import soot.ValueBox;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class LetBindAllocator {
  public final Map<BasicBlock, Map<Local, Binding>> letBind = new HashMap<>();
  public LetBindAllocator(BlockTree<BasicBlock> tree) {
    this.computeBinds(tree);
  }

  private void computeBinds(final BlockTree<BasicBlock> tree) {
    Map<Local, Set<BasicBlock>> use = new HashMap<>();
    Map<Local, Set<BasicBlock>> def = new HashMap<>();
    Map<Local, Integer> writeCounts = new HashMap<>();

    tree.nodes.forEach(bb -> bb.units.forEach(u -> {
          u.getUseBoxes().stream()
              .map(ValueBox::getValue)
              .filter(v -> v instanceof Local)
              .map(v -> (Local) v)
              .forEach(v -> use.merge(v, Collections.singleton(bb), (a1, a2) -> {
                HashSet<BasicBlock> b1 = new HashSet<>(a1);
                b1.addAll(a2);
                return b1;
          }));
          u.getDefBoxes().stream()
              .map(ValueBox::getValue)
              .filter(v -> v instanceof Local)
              .map(v -> (Local)v)
              .forEach(v -> {
                writeCounts.merge(v, 1, (a,b) -> a + b);
                def.merge(v, Collections.singleton(bb), (v1,v2) -> {
                  Set<BasicBlock> m = new HashSet<>(v1); m.addAll(v2); return m;
            });
          });
        }
      ));
    Map<Local, Binding> bindingTypes = new HashMap<>();
    def.keySet().forEach(l -> {
      if(writeCounts.get(l) == 1) {
        // check if each write dominates (is the parent of in the tree) every use.
        // Note that this is trivially true for values used only within the def block
        BasicBlock defBlock = def.get(l).iterator().next();
        boolean dominates = use.getOrDefault(l, Collections.emptySet()).stream().allMatch(useBlock -> {
          BasicBlock it = useBlock;
          while(it != null) {
            if(it.equals(defBlock)) {
              return true;
            }
            it = tree.parent.get(it);
          }
          return false;
        });
        if(dominates) {
          bindingTypes.put(l, Binding.CONST);
        } else {
          bindingTypes.put(l, Binding.MUTABLE);
        }
      } else {
        bindingTypes.put(l, Binding.MUTABLE);
      }
    });
    // now determine where the bindings are introduced
    def.forEach((l, defSites)-> {
      Set<BasicBlock> s = new HashSet<>(defSites);
      if(use.containsKey(l)) {
        s.addAll(use.get(l));
      }
      Set<BasicBlock> levels =  new HashSet<>(s);
      assert levels.size() > 0;
      while(levels.size() != 1) {
        Stream.Builder<BasicBlock> toParent = Stream.builder();
        int maxLevel = levels.stream().collect(Collectors.summarizingInt(tree.level::get)).getMax();
        levels.stream().filter(p -> tree.level.get(p) == maxLevel).forEach(toParent);
        toParent.build().forEach(bb -> {
          levels.remove(bb);
          assert tree.parent.containsKey(bb);
          assert tree.level.get(bb) == maxLevel;
          BasicBlock parent = tree.parent.get(bb);
          assert tree.level.get(parent) == maxLevel - 1;
          levels.add(parent);
        });
      }
      BasicBlock bb = levels.iterator().next();
      letBind.computeIfAbsent(bb, basicBlock -> new HashMap<>()).put(l, bindingTypes.get(l));
    });
  }

}
