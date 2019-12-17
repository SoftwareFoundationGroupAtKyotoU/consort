public class ArrayLoop {
  public static void main(String[] args) {
    int[] x = new int[7];
    for(int i = 0; i < x.length; i++) {
      x[i] = i;
    }
    for(int j = 0; j < x.length; j++) {
      assert x[j] == j;
    }
  }
}
