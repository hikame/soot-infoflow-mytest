package com.kame.sootinfo.mta.tags;
import soot.tagkit.Tag;

public class MySinkTag implements Tag {
	String sinkType;
	
	public MySinkTag(String type){
		sinkType = type;
	}
	
	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "MySinkTag";
	}

    public String getSinkType(){
        return sinkType;
    }
    
    public void setSinkType(String s){
    	sinkType = s;
    }
    
	@Override
    /** Returns the tag raw data. */
    public byte[] getValue() {
        throw new RuntimeException( "StringTag has no value for bytecode" );
    }
}
