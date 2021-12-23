public class find_n_single {
  static void loop(int[] arr, int n, int i, int ans) {
    if (i < arr.length) {
      then1(arr, n, i, ans);
    } else {
      assert_ans(ans);
    }
  }

  static void then1(int[] arr, int n, int i, int ans) {
    if (arr[i] == n) {
      equal_3(ans);
    } else {
      else1(arr, n, i, ans);
    }
  }

  static void else1(int[] arr, int n, int i, int ans) {
    i = i + 1;
    loop(arr, n, i, ans);
  }

  static void equal_3(int ans) {
    ans = 1;
    assert_ans(ans);
  }

  static void assert_ans(int ans) {
    assert (ans == 1);
  }

  public static void main(String[] args) {
    int[] arr = { 0, 9, 3, 4, 15, 16 };
    int n = 3;
    int i = 0;
    int ans = 0;
    loop(arr, n, i, ans);
  }
}
