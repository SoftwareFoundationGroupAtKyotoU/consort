package edu.kyoto.fos.regnant;

import edu.kyoto.fos.regnant.aliasing.FieldAliasing;
import edu.kyoto.fos.regnant.cfg.BasicBlockGraph;
import edu.kyoto.fos.regnant.cfg.BasicBlockMapper;
import edu.kyoto.fos.regnant.cfg.CFGReconstructor;
import edu.kyoto.fos.regnant.simpl.RewriteChain;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import edu.kyoto.fos.regnant.translation.ObjectModel;
import edu.kyoto.fos.regnant.translation.ObjectModel.Impl;
import edu.kyoto.fos.regnant.translation.Translate;
import soot.*;
import soot.options.Options;
import soot.util.queue.ChunkedQueue;
import soot.util.queue.QueueReader;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class Regnant extends Transform {
  private Regnant(final Regnant[] regnants) {
    super("wjtp.regnant", new SceneTransformer() {
      @Override protected void internalTransform(final String phaseName, final Map<String, String> options) {
        regnants[0].internalTransform(phaseName, options);
      }
    });
    regnants[0] = this;
  }

  public static void main(String[] args) {
    PackManager.v().getPack("wjtp").add(new Regnant());
    Options.v().set_verbose(true);
    Main.main(args);
  }

  private Regnant() {
    this(new Regnant[1]);
    setDeclaredOptions("enabled output flags model");
  }

  private void internalTransform(final String phaseName, Map<String, String> options) {
    SootMethod mainMethod = Scene.v().getMainMethod();
    removeArgVector(mainMethod);
    FieldAliasing as = new FieldAliasing();
    for(SootClass sc : Scene.v().getClasses()) {
      if(Scene.v().isExcluded(sc)) {
        continue;
      }
      as.processClass(sc);
    }
    Impl oimpl = ObjectModel.Impl.valueOf(options.getOrDefault("model", "mutable").toUpperCase());
    List<Translate> output = this.transform(mainMethod, as, oimpl);
    try(PrintStream pw = new PrintStream(new FileOutputStream(new File(options.get("output"))))) {
      for(Translate t : output) {
        t.printOn(pw);
      }
      pw.println();
      pw.printf("{ %s() }\n", Translate.getMangledName(mainMethod));
    } catch (IOException ignored) {
    }
//    FlagTranslation.outputTo(options.get("flags"));
  }

  private void removeArgVector(final SootMethod main) {
    assert main.getParameterCount() == 1;
    assert main.getParameterType(0).equals(Scene.v().getSootClass("java.lang.String").getType().makeArrayType());
    assert main.isStatic();
    Local l = main.retrieveActiveBody().getParameterLocal(0);
    Body body = main.getActiveBody();
    UnitPatchingChain units = body.getUnits();
    units.snapshotIterator().forEachRemaining(u -> {
      if(u.getUseBoxes().stream().map(ValueBox::getValue).anyMatch(l::equals)) {
        throw new IllegalArgumentException("Main method uses argument vector");
      }
      if(u.getDefBoxes().stream().map(ValueBox::getValue).anyMatch(l::equals)) {
        units.remove(u);
      }
    });
    body.getLocals().remove(l);
    main.setParameterTypes(List.of());
  }

  private List<Translate> transform(final SootMethod m, final FieldAliasing as, final Impl oimpl) {
    ChunkedQueue<SootMethod> worklist = new ChunkedQueue<>();
    QueueReader<SootMethod> reader = worklist.reader();
    worklist.add(m);
    HashSet<SootMethod> visited = new HashSet<>();
    return this.work(reader, worklist, visited, as, oimpl);
  }

  private List<Translate> work(final QueueReader<SootMethod> reader, final ChunkedQueue<SootMethod> worklist, final HashSet<SootMethod> visited, final FieldAliasing as,
      final Impl oimpl) {
    StorageLayout l = new StorageLayout(Scene.v().getPointsToAnalysis());
    List<Translate> toReturn = new ArrayList<>();
    while(reader.hasNext()) {
      SootMethod m = reader.next();
      if(!visited.add(m)) {
        continue;
      }
      System.out.println("Running regnant transformation on: " + m.getSignature());
      m.retrieveActiveBody();
      Body simpl = RewriteChain.rewrite(m.getActiveBody());
      System.out.println("Simplified: ");
      System.out.println(simpl);
      CFGReconstructor cfg = new CFGReconstructor(simpl);
      BasicBlockMapper bbm = cfg.GetBasicBlockMapper();
      BasicBlockGraph bbg = cfg.GetBasicBlockGraph();
      System.out.println(cfg.dump());

      Translate t = new Translate(simpl, worklist, l, as, oimpl, bbm, bbg);
      toReturn.add(t);
    }
    return toReturn;
  }
}
