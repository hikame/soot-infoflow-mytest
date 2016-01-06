package com.kame.sootinfo.mta.tags;

public class MyStmtTag extends MyMultiThreadTag {

	@Override
	public String getName() {
		return "MyStmtTag";
	}
	
	public MyStmtTag(boolean b) {
		super(b);
	}

}
