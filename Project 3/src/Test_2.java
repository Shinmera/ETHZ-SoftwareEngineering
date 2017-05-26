public class Test_2 {
	public static void m2(int a) {
		Robot r = new Robot(0, 7);
		if (2*a < 9 && a > 0) {
			r.weldBetween(a, a + 1);
			if (a > 5) {
				r.weldAt(a + 4);
			}
		}
	}
}

