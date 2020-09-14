import data.C;

public class ObjectEquality2{
    public static void main(String[] args){
        C a = new C();
        C b = a;
        a.setJ(12);
        
        // if(a == b){
        //     a.setJ(15);
        // }else{
        //     b.setJ(6);
        // }
    }
}