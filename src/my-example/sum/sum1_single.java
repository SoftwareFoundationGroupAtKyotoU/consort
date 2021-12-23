public class sum1_single {
  public static void loop(int i, int sum) {
    if (i < 20) {
      then1(i, sum);
    } else {
      assert_ans(i, sum);
    }
  }

  public static void then1(int i, int sum) {
    sum += i;

    if (sum > 100) {
      assert_ans(i, sum);
    } else {
      else1(i, sum);
    }
  }

  public static void else1(int i, int sum) {
    i++;
    loop(i, sum);
  }

  public static void assert_ans(int i, int sum) {
    assert (sum > 100);
    // System.out.println(i);
    // System.out.println(sum);
  }

  public static void main(String[] args) {
    int i = 0;
    int sum = 0;
    loop(i, sum);
  }
}
