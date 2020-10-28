// ./regnant.py --verbose --work-dir ./alex-tests --src-dir ./alex-tests /Library/Java/JavaVirtualMachines/jdk1.8.0_231.jdk/Contents/Home Simple
public class Simple {
    private Simple s = null;
    public void doIt(Simple s1) {
        this.s = s1;
    }
    public static void main(String[] args) {
        Simple s2 = new Simple();
        Simple s3 = s2;
        s2.doIt(s3);
    }
}
