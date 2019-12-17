public class Loop {
  public static int complexLoop(int a) {
    int toReturn = 0;
    for(int i = 0; i < a || i < 5; i++) {
      toReturn += 2;
    }
    toReturn += 1;
    return toReturn;
  }

  public static void main(String[] args) {
    assert complexLoop(3) == 11 && complexLoop(0) == 11;
    assert complexLoop(1) == 2 || complexLoop(2) == 11;
    assert complexLoop(6) == 13;
  }
}
