package kame.soot;

import java.util.ArrayList;
import java.util.List;

import soot.SootMethodRef;
import soot.jimple.InvokeExpr;

public class UnresolvedClassException extends RuntimeException {
	public UnresolvedClassException(String string) {
		super(string);
	}
	private static final long serialVersionUID = -4042238668437306841L;
	public List<InvokeExpr> mrList = new ArrayList<InvokeExpr>();
}
