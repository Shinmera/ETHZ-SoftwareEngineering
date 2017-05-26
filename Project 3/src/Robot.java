public class Robot {
	private int left, right;

	public Robot(int high) {
		this.right = high;
	}
	
	public Robot(int l, int r) {
		this.left = l;
		this.right = r;
	}

	public native void weldAt(int point);
	public native void weldBetween(int startPoint, int endPoint);
}