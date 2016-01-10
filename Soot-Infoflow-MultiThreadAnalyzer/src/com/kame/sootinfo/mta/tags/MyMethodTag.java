package com.kame.sootinfo.mta.tags;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class MyMethodTag implements Tag {
	boolean isMultithread = false;
	
	@Override
	public String getName() {
		return this.getClass().getSimpleName();
	}
	
	public MyMethodTag(boolean b) {
		isMultithread = b;
	}
	
	public boolean isMultithread(){
		return isMultithread;
	}
	
	public void setmultiThreadFlag(boolean b){
		isMultithread = b;
	}

	@Override
	@Deprecated
	public byte[] getValue() throws AttributeValueException {
		// TODO Auto-generated method stub
		return null;
	}
}
