package com.kame.sootinfo.mta;

import java.util.HashSet;
import java.util.Set;
import soot.jimple.Stmt;

public class MyInvokeTree{
	public Stmt head;
	public Set<MyInvokeTree> chields;	//起始位置的chields为空，而非Null
	
	public MyInvokeTree(){
		head = null;
		chields = new HashSet<MyInvokeTree>();
	}
}