public class sum_square_one_break {
  public static void main(String[] args) {
    int ans = 0;

    for (int i = 0; i < 3; i++) {
      for (int j = 0; j < 3; j++) {
        ans += i + j;
      }
      if (i == 2) break;
    }

    assert(ans == 18);
  }
}
