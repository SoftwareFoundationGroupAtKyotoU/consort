import data.C;

public class ObjectEquality{
    public static void main(String[] args){
        C a = new C();
        C b = a;
        a.setJ(12);
        
        if(a == b){
            assert(a.j == b.j);
        }
    }
}