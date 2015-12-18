package com.kame.tafhd;

import android.util.Log;

public class Publisher {
	String TAG = "KM";
	public void publish(String s){
		System.out.println(s);
		Log.i(TAG, s);
	}
}
