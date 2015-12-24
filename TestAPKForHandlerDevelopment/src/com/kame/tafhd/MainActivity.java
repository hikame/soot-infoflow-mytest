package com.kame.tafhd;

import com.kame.testapkforhandlerdevelopment.R;

import android.app.Activity;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.view.Menu;
import android.view.MenuItem;

public class MainActivity extends Activity {
	class MyHandler extends Handler{
	     @Override
	     public void handleMessage(Message msg) {
	    	 new Publisher().publish("I am in hanlderMessage()");
	    	 switch (msg.what) {
			case TEST_MSG:
				new Publisher().publish((String)msg.obj);
				break;
			case UNRELEVANT_MSG:
				new Publisher().publish("I am in the unrelevent parts.");
				break;
			default:
				break;
			}
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
	
	String tainted;
	Handler mhandler = new MyHandler();
	
	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.activity_main);
		testHandlerPost("TestPost");
		testHandlerSendMSG("TestSendMSG");
	}

	private void testHandlerSendMSG(String s) {
		Message msg = mhandler.obtainMessage(TEST_MSG);
		msg.obj = s;
		mhandler.sendMessage(msg);
	}

	private int getCase() {
		return android.os.Process.myPid();
	}

	private void testHandlerPost(final String s) {
		tainted = s;
//		mhandler.sendEmptyMessage(0);
		Runnable rn = new MyRunnable();
		mhandler.post(rn);
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
