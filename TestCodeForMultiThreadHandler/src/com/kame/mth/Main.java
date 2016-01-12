package com.kame.mth;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.Set;

/**对于Thread：R表示原本soot-info可以识别，W表示我们做了扩展之后可以识别*/
public class Main {	
	String field;
	
	class ParamClass {
		public String fieldString;
		public int fieldInt;
	}
	
//	Thread threadField = new MyThread();
//	Thread threadField;
	MyThread threadField;
	
	class MyThread extends Thread{
		@Override
	    public void run() {
	    	Publisher pl = new Publisher();
			pl.publish(field);
	    }
	}
	
	public static void main(String[] arg) {
		Main main = new Main();
		main.simpleTest("Simple Test");
		
		Method[] mths = Main.class.getDeclaredMethods();
		for(Method mt : mths){
			if(mt.getName().contains("testThread"))
//			if(mt.getName().contains("testHandler"))
				try {
					System.out.println(mt.toString());
					mt.invoke(main, "Test");
				} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
					e.printStackTrace();
				}
		}
	}
	
	public void simpleTest(String s){
		
		System.out.println(this.getClass().getName());
		System.out.println(this.getClass().getSimpleName());
		
		
		String test = "abc;def;ghi;";
		String[] ts = test.split(";");
		
		
		
		Set<String> ints = new HashSet<String>();
		ints.add("1");
		ints.add("2");
		ints.add("3");
		ints.add("4");
//		HashSet<String> ints_clone = new HashSet(ints);
		for(Object str : ints.toArray()){
			System.out.println(str);
			ints.remove(str);
		}
		
		ParamClass pc = new ParamClass();
		System.out.println(pc.fieldInt);
		System.out.println(pc.fieldString);
    	foo(s);
	}
	

	private void foo(String fooStr) {
		Publisher pl = new Publisher();
		pl.publish(fooStr);
	}

	private boolean atest(String s){
    	Publisher pl = new Publisher();
		pl.publish(field);
		return true;
	}
	
	public void testThreadWithField0a(final String s){
		atest(s);
		field = s;
		threadField = new MyThread();
		threadField.start();
	}
	
	public void testThreadWithField0b(final String s){
		field = s;
//		Thread thread = generateThread();
		Thread thread = new MyThread();
		thread.start();
	}
	
	private Thread generateThread() {
		return new MyThread();
	}

	Runnable rn = new Runnable() {
		@Override
		public void run() {
	    	Publisher pl = new Publisher();
			pl.publish(field);
		}
	};
	
	public void testThreadWithField1(final String s){
		field = s;
		Thread thread = new Thread(rn);
		thread.start();
	}
	
	/**R: public Thread() {*/
	public void testThread0(final String s){
		Thread thread = new Thread(){
		    @Override
		    public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
		    }
		};
		thread.start();
	}
	
	/**R: public Thread(Runnable target) {*/
	public void testThread1(final String s){
		Runnable rn = new Runnable(){
			@Override
			public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
			}
		};
		
		Thread thread = new Thread(rn);
		thread.start();
	}

	/**W: public Thread(Runnable target, String name) {*/
	public void testThread2(final String s){
		Runnable rn = new Runnable(){
			@Override
			public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
			}
		};
		
		Thread thread = new Thread(rn, "testThread2");
//		Thread thread = new Thread(rn);
		thread.start();
	}
	
	/**R: public Thread(String name) {*/
	public void testThread3(final String s){
		Thread thread = new Thread("testThread3"){
		    @Override
		    public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
		    }
		};
		thread.start();
	}
	
	/**W: public Thread(ThreadGroup group, Runnable target) {*/
	public void testThread4(final String s){
		ThreadGroup tg = new ThreadGroup("Group-testThread4");
		
		Runnable rn = new Runnable(){
			@Override
			public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
			}
		};
		
		Thread thread = new Thread(tg, rn);
		thread.start();
	}

    /**W: public Thread(ThreadGroup group, Runnable target, String name) {*/
	public void testThread5(final String s){
		ThreadGroup tg = new ThreadGroup("Group-testThread5");
		
		Runnable rn = new Runnable(){
			@Override
			public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
			}
		};
		
		Thread thread = new Thread(tg, rn, "testThread5");
		thread.start();
	}
	
    /**W: public Thread(ThreadGroup group, Runnable target, String name, long stackSize) {*/
	public void testThread6(final String s){
		ThreadGroup tg = new ThreadGroup("Group-testThread6");
		
		Runnable rn = new Runnable(){
			@Override
			public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
			}
		};
		
		Thread thread = new Thread(tg, rn, "testThread6", 1000);
		thread.start();
	}
	
    /**R: public Thread(ThreadGroup group, String name) {*/
	public void testThread7(final String s){
		ThreadGroup tg = new ThreadGroup("Group-testThread7");
		
		Thread thread = new Thread(tg, "testThread7"){
		    @Override
		    public void run() {
		    	Publisher pl = new Publisher();
				pl.publish(s);
		    }
		};
		thread.start();
	}
}
