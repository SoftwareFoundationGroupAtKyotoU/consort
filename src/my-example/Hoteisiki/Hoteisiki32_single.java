public class Hoteisiki32_single {
  public static void loop_x(int x, int y) {
    if (x < 100) {
      then1(x, y);
    } else {
      assert_ans(x, y);
    }
  }

  public static void then1(int x, int y) {
    y = 0;
    loop_y(x, y);
  }

  public static void loop_y(int x, int y) {
    if (y < 100) {
      then2(x, y);
    } else {
      else1(x, y);
    }
  }

  public static void else1(int x, int y) {
    x++;
    loop_x(x, y);
  }

  public static void then2(int x, int y) {
    if (x * x * x + 2 * x * y - 10 * x - y * y == 39) {
      assert_ans(x, y);
    } else {
      else2(x, y);
    }
  }

  public static void else2(int x, int y) {
    y++;
    loop_y(x, y);
  }

  public static void assert_ans(int x, int y) {
    assert (x < 100);
    assert (y < 100);
    // if (x < 100)
    // System.out.println("x = " + x + ",y = " + y);
    // else
    // System.out.println("Not exist");
  }

  public static void main(String[] args) {
    int x = 0, y = 0;
    loop_x(x, y);
  }
}
