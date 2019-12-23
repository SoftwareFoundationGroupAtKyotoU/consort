package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.expr.IntLiteral;
import edu.kyoto.fos.regnant.ir.expr.NullConstant;
import edu.kyoto.fos.regnant.ir.expr.Tuple;
import edu.kyoto.fos.regnant.ir.expr.Variable;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import soot.RefLikeType;
import soot.SootField;
import soot.Type;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public class FunctionalTupleModel implements ObjectModel {
  private StorageLayout layout;

  public FunctionalTupleModel(StorageLayout layout) {
    this.layout = layout;
  }

  @Override public void writeField(final InstructionStream l, final String objectVar, final SootField f, final ImpExpr lhs, final VarManager vm,
      final LinkedList<Cleanup> handlers) {
    int sz = layout.metaStorageSize(f);
    List<String> fields = l.bindProjections(sz, objectVar, vm::getField, layout.getStorageSlot(f));
    assert fields.size() == sz - 1;
    Iterator<String> it = fields.iterator();
    List<ImpExpr> newTuple = new ArrayList<>();
    for(int i = 0; i < sz; i++) {
      if(i == layout.getStorageSlot(f)) {
        newTuple.add(lhs);
      } else {
        assert it.hasNext();
        newTuple.add(Variable.immut(it.next()));
      }
    }
    assert !it.hasNext();
    l.addWrite(objectVar, Tuple.v(newTuple));
  }

  @Override public FieldContents readField(final InstructionStream l, final String objectVar, final SootField f, final VarManager vm, final LinkedList<Cleanup> handlers) {
    int slot = layout.getStorageSlot(f);
    int sz = layout.metaStorageSize(f);
    String v = vm.getField();
    l.bindProjection(v, slot, sz, objectVar);
    return new FieldContents(Variable.immut(v), () -> AliasOp.buildAt(v));
  }

  @Override public Builder extendAP(final Builder b, final SootField f) {
    return b.deref().proj(layout.getStorageSlot(f));
  }

  @Override public ImpExpr allocFieldOfType(final Type t) {
    if(t instanceof RefLikeType) {
      return NullConstant.v();
    } else {
      return IntLiteral.v(0);
    }
  }
}
