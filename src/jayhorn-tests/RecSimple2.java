class RecSimple2
{
    public static class Ptr {
	public int a=0;
    }

    public static void f(Ptr p) {
      p.a += 1;
      if(Havoc_Class.havoc_int()>0){
	  return ;
      }
      else {
          int old = p.a;
	  f(new Ptr());
	  assert(old == p.a);
	  return ;
      }
    }
  public static void main(String[] args)
  {
      Ptr p = new Ptr();
      f(p);
  }
}
