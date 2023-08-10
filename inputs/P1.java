class P1 {
	public static void main(String[] args) {
		try {
			 A x;
			 P1 z;
			 
			 x = new A();
			 z = new P1(); 
			 x.start();
			 x.f = z;
			 x.join();
			 
			}catch (Exception e) {
					
			} 
	}
}
	 
class A extends Thread{
		P1 f;
		
		public void run() {
			try {
				A a;
				P1 b;
				a = this;
				b = new P1();
				a.f = b;
			}catch(Exception e) {
				
			}
		}
	}

