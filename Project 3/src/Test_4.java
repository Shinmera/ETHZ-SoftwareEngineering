public class Test_4 {
    public static void m4(int j) {
        Robot r = new Robot(-2, 6);
        r = new Robot(1, 3);
        if(j < 0){
            r = new Robot(5, 6);
        }
        r.weldAt(3);
    }
}
