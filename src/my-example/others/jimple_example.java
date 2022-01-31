public class jimple_example {
  public static int abs(int x) {
    if (x < 0) {
      return -1 * x;
    } else {
      return x;
    }
  }
  public static void main(String[] args) {
    int x = -3;
    x = 1 + 2 * abs(x);
    assert(x == 7);
  }
}
