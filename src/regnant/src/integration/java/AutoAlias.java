import data.A;
import data.B;

public class AutoAlias {
  public static void main(String[] args) {
    B b = new B();
    b.field = new A();
    b.field.i = 4;
    assert b.field.i == 4;
  }
}
