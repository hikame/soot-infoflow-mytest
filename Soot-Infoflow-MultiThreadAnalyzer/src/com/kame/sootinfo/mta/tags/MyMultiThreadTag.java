package com.kame.sootinfo.mta.tags;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class MyMultiThreadTag implements Tag {

	byte isMultiThread;

	public MyMultiThreadTag(boolean b) {
		this.isMultiThread = (byte) (b ? 1 : 0); 
	}

	@Override
	public String getName() {
		return "MulthThreadTag";
	}

	@Override
	public byte[] getValue() throws AttributeValueException {
		byte[] result = new byte[1];
		result[0] = isMultiThread;
		return result;
	}
	
	public void setValue(boolean b){
		this.isMultiThread = (byte) (b ? 1 : 0);
	}

}
