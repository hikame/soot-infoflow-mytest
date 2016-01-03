package com.kame.tafhd;

import com.kame.testapkforhandlerdevelopment.R;

import android.app.Activity;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.view.Menu;
import android.view.MenuItem;

public class MainActivity extends Activity {
	class ParamClass {
		public String fieldString;
		public int fieldInt;
	}
	
	
	class MyHandler extends Handler{
	     @Override
	     public void handleMessage(Message msg) {
//	    	 new Publisher().publish("I am in hanlderMessage()");
//	    	 if(tainted.length() < 1)
//	    		 return;
	    	switch (msg.what) {
			case TEST_MSG:
//				new Publisher().publish((String)msg.obj + tainted);
				if(msg.obj.equals("0"))
					new Publisher().publish((String)msg.obj);
				else if(msg.obj.equals("1"))
					new Publisher().publish(tainted);
				else return;
//				msg.obj.equals("EqualTest");
				break;
			case UNRELEVANT_MSG:
				new Publisher().publish("I am in the unrelevent parts.");
				break;
			case ANOTHER:
				new Publisher().publish((String)tainted);
				break;
			case OBJ_Publish:
				new Publisher().publish((String)msg.obj);
				break;
			case FIELD_Publish:
				new Publisher().publish(tainted);
				break;
			case FIELD_NP:
				tainted.equals(":");
				break;
			case OBJ_NP:
				msg.obj.equals(":");
			default:
				break;
			}
	     }
	     
	     public void doSinkDirectly(){
	    	 Publisher pb = new Publisher();
	    	 pb.publish(tainted);
	    	 
	    	 tainted.equals("");
	     }
	}
	
	class MyRunnable implements Runnable{
		@Override
		public void run() {
			new Publisher().publish(tainted);
		}
	}

	private static final int TEST_MSG = 0;
	private static final int UNRELEVANT_MSG = 1;
	private static final int ANOTHER = 2;
	private static final int OBJ_Publish = 3;
	private static final int FIELD_Publish = 4;
	private static final int OBJ_NP = 5;
	private static final int FIELD_NP = 6;
	
	String tainted;
	String anOtherField;
	Handler mhandler = new MyHandler();
	
	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.activity_main);
		testHandlerPost(new ParamClass());
		testHandlerSendMSG("TestSendMSG", "TEST2");
	}

	
	private void testHandlerSendMSG(String s0, String s1) {
//		tainted = s0;
////		doSink();
//		((MyHandler) mhandler).doSinkDirectly();
		
		//		Message msg = mhandler.obtainMessage(OBJTEST);
//		msg.obj = s0;
//		mhandler.sendMessage(msg);

		Message msg = mhandler.obtainMessage(OBJ_NP);
		tainted = s0;
		msg.obj = s1;
		mhandler.sendMessage(msg);
		
		
//		Message msg = mhandler.obtainMessage(ANOTHER);
//		tainted = s1;
//		mhandler.sendMessage(msg);
	}

	private void doSink() {
		Publisher pb = new Publisher();
		pb.publish(tainted);
		tainted.equals("");
	}


	private void testHandlerPost(final ParamClass pc) {
		pc.equals("");
		
		tainted = pc.fieldString;
		tainted.equals("");
//		Publisher pub = new Publisher();
////		pub.publish(this.anOtherField);
//		pub.publish(s);
//		mhandler.sendEmptyMessage(0);
//		Runnable rn = new MyRunnable();
//		mhandler.post(rn);
	}

	@Override
	public boolean onCreateOptionsMenu(Menu menu) {
		// Inflate the menu; this adds items to the action bar if it is present.
		getMenuInflater().inflate(R.menu.main, menu);
		return true;
	}

	@Override
	public boolean onOptionsItemSelected(MenuItem item) {
		// Handle action bar item clicks here. The action bar will
		// automatically handle clicks on the Home/Up button, so long
		// as you specify a parent activity in AndroidManifest.xml.
		int id = item.getItemId();
		if (id == R.id.action_settings) {
			return true;
		}
		return super.onOptionsItemSelected(item);
	}
}
