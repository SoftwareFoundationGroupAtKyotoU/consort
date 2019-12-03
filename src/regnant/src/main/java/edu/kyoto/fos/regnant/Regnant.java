package edu.kyoto.fos.regnant;

import edu.kyoto.fos.regnant.cfg.CFGReconstructor;
import edu.kyoto.fos.regnant.cfg.instrumentation.FlagInstrumentation;
import edu.kyoto.fos.regnant.storage.LetBindAllocator;
import edu.kyoto.fos.regnant.translation.Translate;
import soot.Body;
import soot.BodyTransformer;
import soot.Main;
import soot.PackManager;
import soot.Transform;
import soot.options.Options;

import java.util.Map;

public class Regnant {
  public static void main(String[] args) {
    PackManager.v().getPack("jtp").add(new Transform("jtp.regnant", new BodyTransformer() {
      @Override protected void internalTransform(final Body b, final String phaseName, final Map<String, String> options) {
        if(b.getMethod().getName().equals("breakOuter")) {
        System.out.println("Running regnant transformation on: " + b.getMethod().getSignature());
        CFGReconstructor cfg = new CFGReconstructor(b);
        System.out.println(cfg.dump());


          FlagInstrumentation fi = new FlagInstrumentation(cfg);
          LetBindAllocator bindAlloc = new LetBindAllocator(cfg.getStructure());
          Translate t = new Translate(b, cfg.getReconstructedGraph(), fi, bindAlloc);
          t.print();
        }
      }
    }));
    Options.v().set_verbose(true);

    Main.main(args);
  }
}
