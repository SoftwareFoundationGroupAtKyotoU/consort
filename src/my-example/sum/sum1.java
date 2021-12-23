public class sum1 {
  public static void main(String[] args) {
    int i = 0;
    int sum = 0;
    while (i < 20) {
      sum += i;

      if (sum > 100) {
        break;
      }

      i++;
    }

    assert (sum > 100);
    // System.out.println(i);
    // System.out.println(sum);
  }
}
