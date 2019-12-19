package data;

public class A implements ThingGetter {
  public int i, j;
  public int getJ() {
    return j;
  }

  public void setJ(int j) {
    this.j = j;
  }

  @Override public int getThing() {
    return getJ();
  }
}
