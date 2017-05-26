public class Test_3 {
	public static void m3(int a, int b) {
		Robot r = new Robot(-5, 5);
		if (a * b < 5 && a * b > -5 && b != 0) {
			r.weldAt(a + 1);
		}
	}
}
