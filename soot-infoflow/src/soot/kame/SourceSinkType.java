package soot.kame;

public enum SourceSinkType{
	MyTestPublish("MyTestPublish"),
	NullPointerException("java.lang.NullPointerException");
	
	private String name;
	private SourceSinkType(String s){
		name = s;
	}
	
	public String getExceptionClassName(){
		return name;
	}
}