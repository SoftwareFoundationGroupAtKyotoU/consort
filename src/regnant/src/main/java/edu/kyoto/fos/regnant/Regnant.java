package edu.kyoto.fos.regnant;

import edu.kyoto.fos.regnant.cfg.CFGReconstructor;
import edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation;
import edu.kyoto.fos.regnant.simpl.AssertionRewriter;
import edu.kyoto.fos.regnant.simpl.RandomRewriter;
import edu.kyoto.fos.regnant.storage.LetBindAllocator;
import edu.kyoto.fos.regnant.storage.oo.StorageLayout;
import edu.kyoto.fos.regnant.translation.FlagTranslation;
import edu.kyoto.fos.regnant.translation.Translate;
import soot.Body;
import soot.Main;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
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
    setDeclaredOptions("entry enabled output flags");
  }

  private void internalTransform(final String phaseName, Map<String, String> options) {
    if(!options.containsKey("entry")) {
      System.out.println("Regnant: entry point required");
      return;
    }
    String entryPoint = options.get("entry");
    SootClass main = Scene.v().getMainClass();
    assert main.declaresMethodByName(entryPoint);

    SootMethod m = main.getMethodByName(entryPoint);
    List<Translate> output = this.transform(m);
    try(PrintStream pw = new PrintStream(new FileOutputStream(new File(options.get("output"))))) {
      for(Translate t : output) {
        t.printOn(pw);
      }
      pw.println();
      pw.printf("{ %s() }\n", Translate.getMangledName(m));
    } catch (IOException ignored) {
    }
    FlagTranslation.outputTo(options.get("flags"));
  }

  private List<Translate> transform(final SootMethod m) {
    ChunkedQueue<SootMethod> worklist = new ChunkedQueue<>();
    QueueReader<SootMethod> reader = worklist.reader();
    worklist.add(m);
    HashSet<SootMethod> visited = new HashSet<>();
    return this.work(reader, worklist, visited); 
  }

  private List<Translate> work(final QueueReader<SootMethod> reader, final ChunkedQueue<SootMethod> worklist, final HashSet<SootMethod> visited) {
    StorageLayout l = new StorageLayout(Scene.v().getPointsToAnalysis());
    List<Translate> toReturn = new ArrayList<>();
    while(reader.hasNext()) {
      SootMethod m = reader.next();
      if(!visited.add(m)) {
        continue;
      }
      System.out.println("Running regnant transformation on: " + m.getSignature());
      m.retrieveActiveBody();
      Body simpl = RandomRewriter.rewriteRandom(AssertionRewriter.rewrite(m.getActiveBody()));
      System.out.println("Simplified: ");
      System.out.println(simpl);
      CFGReconstructor cfg = new CFGReconstructor(simpl);
      System.out.println(cfg.dump());

      FlagInstrumentation fi = new FlagInstrumentation(cfg);
      LetBindAllocator bindAlloc = new LetBindAllocator(cfg.getStructure());
      Translate t = new Translate(simpl, cfg.getReconstructedGraph(), fi, bindAlloc, worklist, l);
      toReturn.add(t);
    }
    return toReturn;
  }
}
