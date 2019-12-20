package edu.kyoto.fos.regnant.aliasing;

import fj.P;
import fj.P2;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.tagkit.AnnotationArrayElem;
import soot.tagkit.AnnotationConstants;
import soot.tagkit.AnnotationStringElem;
import soot.tagkit.VisibilityAnnotationTag;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class FieldAliasing {
  private Map<SootField,List<List<SootField>>> autoAlias = new HashMap<>();
  private Map<SootField, P2<SootField, SootField>> reverseAlias = new HashMap<>();
  private Set<SootField> finalFields = new HashSet<>();

  public FieldAliasing() {

  }

  public boolean isFinal(SootField f) {
    return finalFields.contains(f);
  }

  public List<P2<List<SootField>, List<SootField>>> getAutoAliasing(SootField f) {
    var toReturn = new ArrayList<P2<List<SootField>, List<SootField>>>();
    autoAlias.getOrDefault(f, Collections.emptyList()).forEach(p -> {
      toReturn.add(P.p(List.of(), p));
    });
    if(reverseAlias.containsKey(f)) {
      var d = reverseAlias.get(f);
      toReturn.add(P.p(List.of(d._1()), List.of(d._2())));
    }
    return toReturn;
  }

  public void processClass(SootClass c) {
    c.getFields().forEach(f -> {
      f.getTags().stream()
          // this to find a single stinking annotation
          .filter(t -> t instanceof VisibilityAnnotationTag)
          .map(t ->(VisibilityAnnotationTag)t)
          .filter(t -> t.getVisibility() == AnnotationConstants.RUNTIME_INVISIBLE)
          .flatMap(t -> t.getAnnotations().stream())
          .filter(annot -> annot.getType().equals("Ledu/kyoto/fos/regnant/annotation/MustAlias;"))
          .flatMap(annotationTag -> annotationTag.getElems().stream())
          .filter(elem -> elem.getName().equals("value"))
          .forEach(elem -> {
            assert elem instanceof AnnotationArrayElem;
            List<String> str = ((AnnotationArrayElem) elem).getValues().stream().map(s -> ((AnnotationStringElem) s).getValue()).collect(Collectors.toList());
            addAliasing(f, str);
          });
    });
  }

  private void addAliasing(final SootField f, final List<String> str) {
    SootClass kls = f.getDeclaringClass();
    if(str.size() > 2) {
      throw new IllegalArgumentException("only aliasing up to depth 1 is supported");
    }
    SootClass it = kls;
    var fit = str.iterator();
    List<SootField> fieldString = new ArrayList<>();
    while(fit.hasNext()) {
      String fldName = fit.next();
      if(!it.declaresFieldByName(fldName)) {
        throw new IllegalArgumentException(String.format("Could not find field %s in class %s (required by annotation %s on field %s)", fldName, it, str, f));
      }
      SootField itField = it.getFieldByName(fldName);
      if(!(itField.getType() instanceof RefLikeType)) {
        throw new IllegalArgumentException(String.format("Field field %s in class %s is not a ref type (required by annotation %s on field %s)", fldName, it, str, f));
      }
      fieldString.add(itField);
      if(fit.hasNext()) {
        if(!(itField.getType() instanceof RefType)) {
          throw new IllegalArgumentException(String.format("Field field %s in class %s is not a class type (required by annotation %s on field %s)", fldName, it, str, f));
        }
        it = ((RefType) itField.getType()).getSootClass();
      }
    }
    // if we made it, this is legit
    this.autoAlias.computeIfAbsent(f, ign -> new ArrayList<>()).add(fieldString);
    finalFields.add(f);
    finalFields.addAll(fieldString);
    if(fieldString.size() == 2) {
      reverseAlias.put(fieldString.get(0), P.p(fieldString.get(1), f));
    }
  }
}
