package minepump;

import edu.kyoto.fos.regnant.annotation.MustAlias;
import edu.kyoto.fos.regnant.runtime.Aliasing;
import minepump.MinePumpSystem.Environment;
import minepump.MinePumpSystem.MinePump;

public class Actions {

  @MustAlias({"p", "env"})
  Environment env;
  MinePump p;

  boolean methAndRunningLastTime = false;
  boolean switchedOnBeforeTS = false;

  Actions() {
    env = new Environment();
    p = new MinePump(env);
  }

  void waterRise() {
    env.waterRise();
  }

  void methaneChange() {
    env.changeMethaneLevel();
  }

  void stopSystem() {
    if(p.isSystemActive())
      p.stopSystem();
  }

  void startSystem() {
    if(!p.isSystemActive())
      p.startSystem();
  }

  void timeShift() {

    p.timeShift();

    if(p.isSystemActive()) {
      Specification1();
    }
  }

  String getSystemState() {
    return p.toString();
  }

  // Specification 1 methan is Critical and pumping leads to Error
  void Specification1() {
    MinePump p = this.p;
    Aliasing.noAutoReturn(p);

    Environment e = p.getEnv();

    boolean b1 = e.isMethaneLevelCritical();
    boolean b2 = p.isPumpRunning();

    Aliasing.alias(e, p, "env");
    Aliasing.alias(e, this, "env");
    Aliasing.alias(p, this, "p");

    if(b1 && b2) {
      assert false;
    }
  }
}
