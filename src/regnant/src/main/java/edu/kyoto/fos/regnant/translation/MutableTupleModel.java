package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.expr.IntLiteral;
import edu.kyoto.fos.regnant.ir.expr.Mkref;
import edu.kyoto.fos.regnant.ir.expr.NullConstant;
import edu.kyoto.fos.regnant.ir.expr.Variable;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import soot.RefLikeType;
import soot.SootField;
import soot.Type;

import java.util.LinkedList;

/*
  Fields are themselves mutable references, hewing closer to the model used by Java.

  Writing is slightly easier than the functional model but not much:
  the pointer of the field must be projected out, written to, and then aliased back in along
  a non-trivial access path.

  Reading is also non-trivial: the reference must be projected out, dereferenced, and then aliased back in.
 */
public class MutableTupleModel implements ObjectModel {
  private final StorageLayout layout;

  public MutableTupleModel(StorageLayout sl) {
    this.layout = sl;
  }

  @Override public void writeField(final InstructionStream l, final String objectVar, final SootField f, ImpExpr lhs, final VarManager vm, final LinkedList<Cleanup> handlers) {
    int slot = layout.getStorageSlot(f);
    int d = layout.metaStorageSize(f);
    String fld = vm.getField();
    l.bindProjection(fld, slot, d, objectVar);
    l.addWrite(fld, lhs);
    addCleanup(objectVar, handlers, slot, fld);
  }

  @Override public FieldContents readField(final InstructionStream l, final String objectVar, final SootField f, final VarManager vm, final LinkedList<Cleanup> handlers) {
    int slot = layout.getStorageSlot(f);
    int d = layout.metaStorageSize(f);
    String fld = vm.getField();
    l.bindProjection(fld, slot, d, objectVar);
    addCleanup(objectVar, handlers, slot, fld);
    ImpExpr e = Variable.deref(fld);
    return new FieldContents(e, () -> AliasOp.buildAt(fld).deref());
  }

  private void addCleanup(final String objectVar, final LinkedList<Cleanup> handlers, final int slot, final String fld) {
    handlers.push(i -> i.addPtrProjAlias(fld, objectVar, slot));
  }

  /*
    Builder points to the object value
   */
  @Override public Builder extendAP(final Builder b, final SootField f) {
    // object -(deref)> tuple -(proj)> field ref -(deref)> value
    return b.deref().proj(this.layout.getStorageSlot(f)).deref();
  }

  @Override public ImpExpr allocFieldOfType(final Type t) {
    if(t instanceof RefLikeType) {
      return new Mkref(NullConstant.v());
    } else {
      return new Mkref(IntLiteral.v(0));
    }
  }
}
