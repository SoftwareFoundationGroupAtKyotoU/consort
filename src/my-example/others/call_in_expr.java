public class call_in_expr {
  public static int plus2(int x) {
    return x + 2;
  }
  public static void main(String[] args) {
    int x = 0;

    for (int i = 0; i < 10; i++) {
      x = plus2(x);
    }

    assert(x == 20);
  }
}
