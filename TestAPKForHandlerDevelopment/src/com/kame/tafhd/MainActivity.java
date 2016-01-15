package com.kame.tafhd;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import com.kame.testapkforhandlerdevelopment.R;

import android.app.Activity;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.view.Menu;
import android.view.MenuItem;

public class MainActivity extends Activity {
	private native void nativeMethod(String param);
	
	static String staticTaint;
	String tainted;
	String anOtherField;
	Handler mhandler = new MyHandler();
	
	ClassX taintedXField;
	
	class ParamClass {
		public String fieldString;
		public int fieldInt;
	}
	
	class ClassX {
		public ClassY objY;
		public int fieldInt;
		public String fieldString;
		public ParamClass objPC;
	}
	
	class ClassY{
		public String tainted;
	}
	
	
	class MyHandler extends Handler{
	     @Override
	     public void handleMessage(Message msg) {
//	    	 new Publisher().publish("I am in hanlderMessage()");
//	    	 if(tainted.length() < 1)
//	    		 return;
//	    	 doHandlerMessage(msg.what);
	    	 doHandlerMessageBasedOnWhat(msg.what);
	     }
	     
	     private void doHandlerMessageBasedOnWhat(int wt) {
	    	switch (wt) {
			case TEST_MSG:
				Publisher pub = new Publisher();
				pub.publish(tainted);
				break;
			case STATIC_FIELD_NULL:
				staticTaint.equals("");
				break;
			default:
				break;
	    	}
				
		}

		private void doHandlerMessage(Message msg) {
		    	switch (msg.what) {
				case TEST_MSG:
					Publisher pub = new Publisher();
					ClassX x = (ClassX) msg.obj;
					pub.publish(x.objY.tainted);
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
					tainted.equals("");
//					doNull(tainted);
					break;
				case OBJ_NP:
					Object loc = msg.obj;
//					if(loc != null){
//						loc.equals("if");
//		    		}	
//		    		loc.equals("2");
//					if(loc != null)
						doNull(loc);
					break;
				case NEW_NULL:
//					if(tainted != null)
//						tainted.equals("");
//			    	 Publisher pb = new Publisher();
//			    	 pb.publish(tainted);
					if(tainted != null){
						Publisher pb = new Publisher();
				    	 pb.publish(tainted);
					}
						tainted.equals("");
					break;
					
				case STATIC_FIELD_NULL:
					staticTaint.equals("");
					//------------------
//					ClassX objx = new ClassX();
//					objx.objY = null;
//					objx.fieldString = (String) msg.obj;
//					objx.equals("");
//					objx.objY.equals("");
//					objx.fieldString.equals("");
//					break;
					
				default:
					break;
				}
		}

		private String getTainted() {
	    	 if(tainted != null)
	    		 return tainted;
	    	 else
	    		 return "";
		}

		private void doNull(Object myobj) {
//			if(myobj != null)
				tainted.equals("");
				
		}

		private void letsDoNP(Object orz) throws IOException  {

		    	 File orzF = new File(orz.toString());
		    	 FileWriter orgFW = null;
				orgFW = new FileWriter(orzF);
		    	orgFW.toString();

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
			String str = taintedXField.objPC.fieldString;
			new Publisher().publish(str);
		}
	}

	private static final int TEST_MSG = 0;
	private static final int UNRELEVANT_MSG = 1;
	private static final int ANOTHER = 2;
	private static final int OBJ_Publish = 3;
	private static final int FIELD_Publish = 4;
	private static final int OBJ_NP = 5;
	private static final int FIELD_NP = 6;
	private static final int NEW_NULL = 7;
	private static final int STATIC_FIELD_NULL = 8;
	
	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.activity_main);
		testHandlerPost(new ParamClass());
		testHandlerSendMSG("TestSendMSG");
	}

	
//	private void testHandlerSendMSG(String s0, String s1) {
	private void testHandlerSendMSG(String s0) {
//		Message msg = mhandler.obtainMessage(STATIC_FIELD_NULL);
		Message msg = mhandler.obtainMessage(FIELD_NP);
//		msg.wh
//		msg.obj = s0;
//		if(msg.obj != null)
//		if(s0 != null)
			staticTaint = s0;
//			tainted = s0;
		mhandler.sendEmptyMessage(STATIC_FIELD_NULL);
		

//		Message msg = mhandler.obtainMessage(FIELD_NP);
////		msg.obj = s0;
////		if(msg.obj != null)
//		nativeMethod(s0);
//		mhandler.sendMessage(msg);
//		tainted = s0;
//		if(s1 != null)
//			staticTaint = s1;
	}

	private void doSink() {
		Publisher pb = new Publisher();
		pb.publish(tainted);
		tainted.equals("");
	}


	private void testHandlerPost(final ParamClass pc) {
//		pc.equals("");
		ClassX objX = new ClassX();
		objX.objPC = pc;
		taintedXField = objX;
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
