public class find_n {
  public static void main(String[] args) {
    int[] arr = { 0, 9, 3, 4, 15, 16 };
    int n = 2;
    int i = 0;
    int ans = 0;

    while (i < arr.length) {
      if (arr[i] == n) {
        ans = 1;
        break;
      }
      i++;
    }

    assert (ans == 1);
  }
}