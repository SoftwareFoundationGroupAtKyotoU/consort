package minepump.MinePumpSystem;

public class MinePump {

  boolean pumpRunning = false;

  boolean systemActive = true;

  Environment env;

  public MinePump(Environment env) {
    super();
    this.env = env;
  }

  public void timeShift() {
    if(pumpRunning)
      env.lowerWaterLevel();
    if(systemActive)
      processEnvironment();
  }

  void processEnvironment() {

  }

  void activatePump() {
    pumpRunning = true;
  }

  public boolean isPumpRunning() {
    return pumpRunning;
  }

  void deactivatePump() {
    pumpRunning = false;
  }

  boolean isMethaneAlarm() {
    return env.isMethaneLevelCritical();
  }

  @Override public String toString() {
    return "Pump(System:" + (systemActive ? "On" : "Off") + ",Pump:" + (pumpRunning ? "On" : "Off") + ") " + env.toString();
  }

  public Environment getEnv() {
    return env;
  }

  public void stopSystem() {
    // feature not present
  }

  public void startSystem() {
    // feature not present
  }

  public boolean isSystemActive() {
    return systemActive;
  }

}

