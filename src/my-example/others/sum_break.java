public class sum_break {
  public static void main(String[] args) {
    int sum = 0;
    int ans = 0;

    for (int i = 0; i < 5; i++) {
      for (int j = 0; j < 5; j++) {
        sum += i + j;
        ans++;

        if (sum > 15) {
          break;
        }
      }

      if (sum > 15) {
        break;
      }
    }

    assert (ans == 8);
  }
}
