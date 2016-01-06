package com.kame.sootinfo.mta.tags;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class MyMethodTag extends MyMultiThreadTag {

	@Override
	public String getName() {
		return "MyMethodTag";
	}
	
	public MyMethodTag(boolean b) {
		super(b);
	}
}
