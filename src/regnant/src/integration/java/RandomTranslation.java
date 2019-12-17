import annotation.ExpectFail;

import java.util.Random;

public class RandomTranslation {
  @ExpectFail
  public static void main(String[] args) {
    int x = new Random().nextInt();
    assert x == 4;
  }
}
