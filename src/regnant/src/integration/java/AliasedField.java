import data.A;

public class AliasedField {
  public static void main(String[] args) {
    A a = new A();
    A b = a;
    setField(a, 5);
    b.j = a.i + 6;
    assert a.i == 5;
    assert b.j == 11;
  }

  private static void setField(final A a, final int i) {
    a.i = i;
  }
}
