import edu.kyoto.fos.regnant.annotation.MustAlias;

public class MustAliasAnnot {
  private static class Target {
    int st2 = 3;

    public void step() {
      st2++;
    }

    public int state() {
      return st2;
    }

    public Target() {

    }
  }
  private static class SubContainer {
    Target t;
    int st;

    public SubContainer(Target t) {
      this.t = t;
      this.st = 0;
    }

    public void step() {
      if(this.st++ == 0) {
        return;
      }
      this.t.step();
    }
  }
  public static class Container {
    @MustAlias({"f", "t"})
    public Target x;

    public SubContainer f;

    public Container() {
      this.x = new Target();
      this.f = new SubContainer(this.x);
    }

    public void action() {
      f.step();
    }

    public void shift() {
      this.x.step();
    }

    public int state() {
      return this.x.state();
    }
  }

  public static void main(String[] args) {
    Container c = new Container();
    c.action();
    c.action();
    c.shift();
    assert c.state() == 5;
  }
}
