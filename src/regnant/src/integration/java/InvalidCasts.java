import annotation.ExpectFail;
import data.Sub;
import data.Super;
import data.Unreachable;

import java.util.Random;

public class InvalidCasts {
  @ExpectFail public static void main(String[] args) {
    Random r = new Random();
    int x = r.nextInt();
    Super l;
    if(x == 5) {
      l = new Unreachable();
    } else {
      l = new Sub();
    }
    if(x == 5) {
      Sub s = (Sub) l;
      assert s.getThing() == 3;
    } else {
      Unreachable u = (Unreachable) l;
      assert u.getThing() == 2;
    }
  }
}
