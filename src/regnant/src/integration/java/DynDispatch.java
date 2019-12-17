import data.Sub;
import data.Super;

import java.util.Random;

public class DynDispatch {
  public static void main(String[] args) {
    Super s;
    Random r = new Random();
    if(r.nextInt() == 0) {
      s = new Super();
    } else {
      s = new Sub();
    }
    assert s.getThing() <= 4;
    assert s.getThing() >= 3;
  }
}
