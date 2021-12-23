public class sum2_break {
  public static void main(String[] args) {
    int ans = 0, i = 0, j = 0;
    while (i < 10) {
      j = 0;
      while (j < 10) {
        ans += i * j;
        if (ans > 100) {
          break;
        }
        j++;
      }
      if (ans > 100) {
        break;
      }
      i++;
    }

    assert (i < 10);
    assert (j < 10);
    // System.out.println(i);
    // System.out.println(j);
  }
}
