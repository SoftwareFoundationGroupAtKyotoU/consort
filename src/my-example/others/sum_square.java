public class sum_square {
  public static void main(String[] args) {
    int ans = 0;

    for (int i = 0; i < 3; i++) {
      for (int j = 0; j < 3; j++) {
        ans += i + j;
      }
    }

    assert(ans == 18);
  }
}
