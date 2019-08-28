class RecSimple
{
    public static class Ptr {
	public int a;
    }

    public static boolean f(Ptr p) {
      int old = p.a;
      if(Havoc_Class.havoc_int()>0){
	  return true;
      }
      else {
	  Ptr pb = new Ptr();
	  pb.a = Havoc_Class.havoc_int();
	  boolean res = f(pb);
	  return(res & (old == p.a));
      }
    }
  public static void main(String[] args)
  {
      Ptr p = new Ptr();
      assert(f(p));
  }
}
