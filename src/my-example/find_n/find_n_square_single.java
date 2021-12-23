public class find_n_square_single {
  public static void loop1(int[] arr, int n, int i, int j, int ans) {
    if (i < 3) {
      then1(arr, n, i, j, ans);
    } else {
      assert_ans(ans);
    }
  }

  public static void then1(int[] arr, int n, int i, int j, int ans) {
    j = 0;
    loop2(arr, n, i, j, ans);
  }

  public static void loop2(int[] arr, int n, int i, int j, int ans) {
    if (j < 3) {
      then2(arr, n, i, j, ans);
    } else {
      else1(arr, n, i, j, ans);
    }
  }

  public static void then2(int[] arr, int n, int i, int j, int ans) {
    if (arr[3 * i + j] == n) {
      then3(arr, n, i, j, ans);
    } else {
      else2(arr, n, i, j, ans);
    }
  }

  public static void then3(int[] arr, int n, int i, int j, int ans) {
    ans = 1;
    else1(arr, n, i, j, ans);
  }

  public static void else2(int[] arr, int n, int i, int j, int ans) {
    j++;
    loop2(arr, n, i, j, ans);
  }

  public static void else1(int[] arr, int n, int i, int j, int ans) {
    if (arr[3 * i + j] == n) {
      then4(arr, n, i, j, ans);
    } else {
      else3(arr, n, i, j, ans);
    }
  }

  public static void then4(int[] arr, int n, int i, int j, int ans) {
    ans = 1;
    assert_ans(ans);
  }

  public static void else3(int[] arr, int n, int i, int j, int ans) {
    i++;
    loop1(arr, n, i, j, ans);
  }

  public static void assert_ans(int ans) {
    assert (ans == 1);
  }

  public static void main(String[] args) {
    int[] arr = { 0, 9, 3, 4, 15, 16, 8, 7, 20 };
    int n = 3;
    int i = 0;
    int j = 0;
    int ans = 0;
    loop1(arr, n, i, j, ans);
  }
}
