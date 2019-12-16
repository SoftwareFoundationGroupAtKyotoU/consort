package edu.kyoto.fos.regnant.storage.oo;

import edu.kyoto.fos.regnant.storage.oo.UnionFind.Node;
import soot.PointsToAnalysis;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.Type;
import soot.jimple.spark.pag.LocalVarNode;
import soot.jimple.spark.pag.PAG;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class StorageLayout {
  private UnionFind<SootClass> uf = new UnionFind<>();

  public StorageLayout(PointsToAnalysis pta) {
    this.analyze(pta);
  }

  private void analyze(final PointsToAnalysis pta) {
    assert pta instanceof PAG;
    PAG pag = (PAG) pta;
    unifyRepr(pag.allocSources().stream().flatMap(n -> n.getAllFieldRefs().stream()));
    unifyRepr(pag.simpleInvSources().stream());

    uf.universe().forEach(sc -> sc.getFields().forEach(sf -> {
      addMetaField(uf.find(sc).getData(), sf);
    }));
    
    this.assignSlots();
  }

  private Map<SootField, Integer> fieldSlots = new HashMap<>();
  private Map<SootClass, List<SootField>> metaLayout = new HashMap<>();
  private Map<SootField, SootClass> invMeta = new HashMap<>();

  private void assignSlots() {
    Comparator<SootField> cmp = Comparator.comparingInt((SootField sf) -> sf.getType() instanceof RefLikeType ? 0 : 1).thenComparing(
        (Function<? super SootField, ? extends String>) SootField::getSignature);
    metaClasses.forEach((meta, fields) -> {
      List<SootField> f = fields.stream().sorted(cmp).collect(Collectors.toList());
      metaLayout.put(meta, f);
      for(int i = 0; i < f.size(); i++) {
        assert !fieldSlots.containsKey(f.get(i));
        fieldSlots.put(f.get(i), i + 1);
        invMeta.put(f.get(i), meta);
      }
    });
  }

  public boolean haveSameRepr(Stream<SootClass> str) {
    var d = str.map(uf::find).map(Optional::<UnionFind.Node<SootClass>>of).reduce((o1, o2) -> o1.flatMap(n1 -> o2.flatMap(n2 -> {
      if(n1.getData().equals(n2.getData())) {
        return Optional.of(n1);
      } else {
        return Optional.<UnionFind.Node<SootClass>>empty();
      }
    })));
    return d.flatMap(i -> i).isPresent();
  }

  private Map<SootClass, Set<SootField>> metaClasses = new HashMap<>();

  private void addMetaField(final SootClass data, final SootField sf) {
    metaClasses.computeIfAbsent(data, ign -> new HashSet<>()).add(sf);
  }

  private void unifyRepr(final Stream<? extends soot.jimple.spark.pag.Node> nodeStream) {
    nodeStream.forEach(adf -> {
      if(adf instanceof LocalVarNode) {
        LocalVarNode varNode = (LocalVarNode) adf;
        if(varNode.getMethod().getDeclaringClass().getName().equals("java.lang.Object")) {
          return;
        }
      }
      Set<Type> types = adf.getP2Set().possibleTypes();
      Optional<SootClass> n = types.stream().filter(RefType.class::isInstance).map(RefType.class::cast).map(RefType::getSootClass).map(uf::find).reduce(uf::union).map(Node::getData);
    });
  }

  public List<SootField> getMetaLayout(SootClass kls) {
    SootClass meta = uf.find(kls).getData();
    assert metaLayout.containsKey(meta);
    return metaLayout.get(meta);
  }

  public int getStorageSlot(SootField f) {
    assert fieldSlots.containsKey(f);
    assert fieldSlots.get(f) > 0;
    return fieldSlots.get(f);
  }

  public int metaStorageSize(SootField f) {
    SootClass kls = invMeta.get(f);
    // plus the runtime tag
    return metaLayout.get(kls).size() + 1;
  }

  public int metaStorageSize(final SootClass klassSz) {
    SootClass meta = uf.find(klassSz).getData();
    return metaLayout.get(meta).size() + 1;
  }
}
