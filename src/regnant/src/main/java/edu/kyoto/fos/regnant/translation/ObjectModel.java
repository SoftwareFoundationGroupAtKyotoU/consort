package edu.kyoto.fos.regnant.translation;

import edu.kyoto.fos.regnant.ir.expr.ImpExpr;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp;
import edu.kyoto.fos.regnant.ir.stmt.aliasing.AliasOp.Builder;
import soot.SootField;
import soot.Type;

import java.util.LinkedList;

public interface ObjectModel {
  void writeField(InstructionStream l, String objectVar, SootField f, ImpExpr lhs, VarManager vm, LinkedList<Cleanup> handlers);
  FieldContents readField(InstructionStream l, String objectVar, SootField f, VarManager vm, LinkedList<Cleanup> handlers);

  Builder extendAP(AliasOp.Builder b, SootField f);

  default void iterAP(SootField f, AliasOp.Builder b) {
    extendAP(b, f);
  }
  ImpExpr allocFieldOfType(Type t);
}
