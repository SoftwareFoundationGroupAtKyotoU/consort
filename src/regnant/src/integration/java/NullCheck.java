import annotation.ExpectFail;
public class NullCheck {
    @ExpectFail
    public static void main(String[] args){
        String s = null;
        
        assert((s != null));
    }
}