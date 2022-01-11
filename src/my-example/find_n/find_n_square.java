public class find_n_square {
  public static void main(String[] args) {
    int[] arr = { 0, 9, 3, 4, 15, 16, 8, 7, 20 };
    int n = 2;
    int i = 0;
    int j = 0;
    int ans = 0;

    while (i < 3) {
      j = 0;
      while (j < 3) {
        if (arr[3 * i + j] == n) {
          ans = 1;
          break;
        }
        j++;
      }
      if (arr[3 * i + j] == n) {
        ans = 1;
        break;
      }
      i++;
    }

    assert (ans == 1);
  }
}
