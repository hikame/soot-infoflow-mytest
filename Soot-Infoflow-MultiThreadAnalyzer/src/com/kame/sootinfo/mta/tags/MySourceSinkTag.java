package com.kame.sootinfo.mta.tags;
import com.kame.sootinfo.mta.MyInvokeTree;

import soot.tagkit.Tag;

public class MySourceSinkTag implements Tag {
	String sinkType;
	
	MyInvokeTree sourceActiveInvokeTree;
	
	public MySourceSinkTag(String type){
		sinkType = type;
	}
	
	@Override
	public String getName() {
		return this.getClass().getSimpleName();
	}

    public String getSourceSinkType(){
        return sinkType;
    }
    
    public void setSourceSinkType(String s){
    	sinkType = s;
    }
    
    public MyInvokeTree getSourceActiveInvokeTree(){
    	return sourceActiveInvokeTree;
    }
    
    public void setSourceActiveInvokeTree(MyInvokeTree mit){
    	sourceActiveInvokeTree = mit;
    }
    
	@Override
    /** Returns the tag raw data. */
    public byte[] getValue() {
        throw new RuntimeException( "StringTag has no value for bytecode" );
    }
}
