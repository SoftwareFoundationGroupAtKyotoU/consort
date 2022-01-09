public class my_example2 {
  public static void main(String[] args) {
    int ans = 0;

    for (int i = 0; i < 10; i++) {
      if (i % 3 == 0) {
        continue;
      }

      ans += i;
    }

    assert(ans == 37);
  }
}
