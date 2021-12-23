public class Hoteisiki31 {
  public static void main(String[] args) {
    int x;
    for (x = 0; x < 100; x++) {
      if (x * x - 145 * x + 3616 == 0)
        break; // この break文が実行されると
    } // 4〜6 行目の for 文が終了する
    assert (x < 100);
    // if (x < 100)
    // System.out.println(x);
    // else
    // System.out.println("Not exist");
  }
}
