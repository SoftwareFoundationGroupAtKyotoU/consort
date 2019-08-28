class LoopSimple
{
    public static class Ptr {
	public int a=0;
    }

  public static void main(String[] args)
  {
      int n = Havoc_Class.havoc_int();
      int i=0;
      int last=0;
      Ptr q = new Ptr();
      if(n>0) {
	  for(i=0; i<n; i++) {
              Ptr p = new Ptr();
	      p.a = 1;
	      q = p;
	  };
	  assert(q.a==1);
      }
  }
}
