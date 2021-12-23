public class sum2 {
  public static void main(String[] args) {
    int ans = 0, i = 0, j = 0;
    outer: while (i < 10) {
      j = 0;
      while (j < 10) {
        ans += i * j;
        if (ans > 100) {
          break outer;
        }
        j++;
      }
      i++;
    }

    assert (i < 10);
    assert (j < 10);
    // System.out.println(i);
    // System.out.println(j);
  }
}
