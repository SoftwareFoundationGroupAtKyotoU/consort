import data.A;
import data.Super;
import data.ThingGetter;

import java.util.Random;

public class InterfaceTest {
  public static void main(String[] args) {
    Random r = new Random();
    int bound = r.nextInt();
    A a = new A();
    a.setJ(4);
    ThingGetter tg = a;
    for(int i = 0; i < bound; i++) {
      ThingGetter tprime;
      if(r.nextInt() == 0) {
        tprime = new Super();
      } else {
        a = new A();
        a.setJ(4);
        tprime = a;
      }
      if(r.nextInt() == 0) {
        tg = tprime;
      }
    }
    assert tg.getThing() == 4;
    if(tg instanceof A) {
      A b = (A) tg;
      assert b.i == 0;
    }
  }
}
