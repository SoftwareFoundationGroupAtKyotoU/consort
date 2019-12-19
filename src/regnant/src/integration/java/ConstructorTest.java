public class ConstructorTest {
  
  public static class Constr {
    public final int j;
    public final int i;

    public Constr(int i, int j) {
      this.i = i;
      this.j = j;
    }
  }
  public static void main(String[] args) {
    Constr c = new Constr(6, 7);
    assert c.i + c.j == 13;
  }
}
