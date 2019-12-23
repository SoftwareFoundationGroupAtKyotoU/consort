package minepump.MinePumpSystem;

public  class  Environment {



  private int waterLevel = 1;



  private boolean methaneLevelCritical = false;



  void lowerWaterLevel() {
    if(waterLevel == 2) {
      waterLevel = 1;
    } else if(waterLevel == 1) {
      waterLevel = 0;
    }
    /*
    Manual unrolling of switch
    switch (waterLevel) {
    case 2:
      waterLevel = 1;
      break;
    case 1:
      waterLevel = 0;
      break;
    }*/
  }



  public void waterRise() {
    if(waterLevel == 0) {
      waterLevel = 1;
    } else if(waterLevel == 1) {
      waterLevel = 2;
    }
    /*
    switch (waterLevel) {
    case 0:
      waterLevel = 1;
      break;
    case 1:
      waterLevel = 2;
      break;
    }
    */
  }



  public void changeMethaneLevel() {
    methaneLevelCritical = !methaneLevelCritical;
  }



  public boolean isMethaneLevelCritical() {
    return methaneLevelCritical;
  }



  @Override
  public String toString() {
    return "Env(Water:" + waterLevel + ",Meth:" + (methaneLevelCritical?"CRIT":"OK") + ")";
  }



  public int getWaterLevel() {
    return waterLevel;
  }


  boolean isLowWaterSensorDry() {
    return waterLevel == 0;
  }

  boolean isHighWaterSensorDry() {
    return waterLevel != 2;
  }

}
