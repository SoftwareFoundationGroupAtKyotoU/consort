public class Hoteisiki32 {
  public static void main(String[] args) {
    int x = 0, y = 0;
    out: for (x = 0; x < 100; x++) {
      for (y = 0; y < 100; y++) {
        if (x * x * x + 2 * x * y - 10 * x - y * y == 39)
          break out;
      }
    }
    assert (x < 10);
    assert (y < 10);
    // if (x < 100)
    // System.out.println("x = " + x + ",y = " + y);
    // else
    // System.out.println("Not exist");
  }
}
