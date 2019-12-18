import data.A;
import data.B;

public class AutoAliasMethod {
  public static void main(String[] args) {
    B b = new B();
    b.field = new A();
    b.field.setJ(5);
    assert b.field.j == 5;
  }
}
