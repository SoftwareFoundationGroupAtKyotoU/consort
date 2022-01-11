public class sum_goto {
  public static void main(String[] args) {
    int sum = 0;
    int ans = 0;

    out: for (int i = 0; i < 5; i++) {
      for (int j = 0; j < 5; j++) {
        sum += i + j;
        ans++;

        if (sum > 15) {
          break out;
        }
      }
    }

    assert (ans == 8);
  }
}
