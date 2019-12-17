import data.A;

public class SetterGetter {
  public static void main(String[] args) {
    A a = new A();
    a.setJ(5);
    assert a.getJ() == 5;
  }
}
