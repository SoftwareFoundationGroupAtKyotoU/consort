public class sum2_single {
  public static void loop1(int ans, int i, int j) {
    if (i < 10) {
      then1(ans, i, j);
    } else {
      assert_ans(i, j);
    }
  }

  public static void then1(int ans, int i, int j) {
    j = 0;
    loop2(ans, i, j);
  }

  public static void loop2(int ans, int i, int j) {
    if (j < 10) {
      then2(ans, i, j);
    } else {
      else1(ans, i, j);
    }
  }

  public static void else1(int ans, int i, int j) {
    i++;
    loop1(ans, i, j);
  }

  public static void then2(int ans, int i, int j) {
    ans += i * j;
    if (ans > 100) {
      assert_ans(i, j);
    } else {
      else2(ans, i, j);
    }
  }

  public static void else2(int ans, int i, int j) {
    j++;
    loop2(ans, i, j);
  }

  public static void assert_ans(int i, int j) {
    assert (i < 10);
    assert (j < 10);
    // System.out.println(i);
    // System.out.println(j);
  }

  public static void main(String[] args) {
    int ans = 0, i = 0, j = 0;
    loop1(ans, i, j);
  }
}
