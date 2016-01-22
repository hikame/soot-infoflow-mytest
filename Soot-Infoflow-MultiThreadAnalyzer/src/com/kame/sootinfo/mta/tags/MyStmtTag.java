package com.kame.sootinfo.mta.tags;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.kame.sootinfo.mta.MyInvokeTree;

import soot.Value;
import soot.jimple.Stmt;
import soot.kame.SourceSinkType;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class MyStmtTag implements Tag{
	/**TODO: This seems unnecessary if the AccessPath is extended with Set<SourceSinkType> sourceTypes*/
	Map<Value, Set<SourceSinkType>> sourceTypeOfValues = new HashMap<Value, Set<SourceSinkType>>();
	Set<SourceSinkType> sinkTypes = new HashSet<SourceSinkType>();
	MyInvokeTree sourceActiveInvokeTree;

	@Override
	public String getName() {
		return this.getClass().getSimpleName();
	}
	
	/**add/remove operation on the return value will be reflacted in this tag, too.*/
	
	public Set<SourceSinkType> getSourceTypes(Value v){
		return this.sourceTypeOfValues.get(v);
	}

	/**add/remove operation on the return value will be reflacted in this tag, too.*/
	public Set<SourceSinkType> getSinkTypes(){
		return this.sinkTypes;
	}
	
	@Override
	@Deprecated
	/**Unused!*/
	public byte[] getValue() throws AttributeValueException {
		return null;
	}

	@Override
	public MyStmtTag clone(){
		MyStmtTag result = new MyStmtTag();
		result.sinkTypes.addAll(this.sinkTypes);
		for(Value key : this.sourceTypeOfValues.keySet())
			result.sourceTypeOfValues.put(key, this.sourceTypeOfValues.get(key));
		return result;
	}

	public static MyStmtTag getTagFrom(Stmt sCallSite) {
		MyStmtTag result = (MyStmtTag) sCallSite.getTag(MyStmtTag.class.getSimpleName());
		if(result == null){
			result = new MyStmtTag();
			sCallSite.addTag(result);
		}
		return result;
	}
	
    public MyInvokeTree getSourceActiveInvokeTree(){
    	return sourceActiveInvokeTree;
    }
    
    public void setSourceActiveInvokeTree(MyInvokeTree mit){
    	sourceActiveInvokeTree = mit;
    }
}
