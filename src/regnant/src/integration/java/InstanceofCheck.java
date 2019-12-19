import data.Sub;
import data.Super;
import data.Unreachable;

import java.util.Random;

public class InstanceofCheck {
  public static void main(String[] args) {
    Super s;
    Random r = new Random();
    if(r.nextInt() == 1) {
      s = new Sub();
    } else {
      s = new Unreachable();
    }
    if(s instanceof Sub) {
      Sub sub = (Sub) s;
      assert sub.getThing() == 3;
    }
    boolean b = s instanceof Super;
    assert(b == true);
  }
}
