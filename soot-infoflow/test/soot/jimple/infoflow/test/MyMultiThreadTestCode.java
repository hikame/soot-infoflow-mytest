package soot.jimple.infoflow.test;
import soot.jimple.infoflow.test.android.AccountManager;
import soot.jimple.infoflow.test.android.ConnectionManager;

public class MyMultiThreadTestCode {
	private String field;
	private MyThread threadField;
	
	class MyThread extends Thread{
		@Override
	    public void run() {
			ConnectionManager cm = new ConnectionManager();
			cm.publish(field);
	    }
	}
	

	public void testThreadWithField0a(final String s){
		AccountManager am = new AccountManager();
		field = am.getPassword();
		threadField = new MyThread();
		threadField.start();
	}
	
	public void testThreadWithField0b(final String s){
		AccountManager am = new AccountManager();
		field = am.getPassword();
		MyThread thread = new MyThread();
		thread.start();
	}
}
