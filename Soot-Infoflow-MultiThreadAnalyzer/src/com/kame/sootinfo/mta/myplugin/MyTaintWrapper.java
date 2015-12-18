package com.kame.sootinfo.mta.myplugin;

import java.util.Set;

import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;

public class MyTaintWrapper implements ITaintPropagationWrapper {

	@Override
	public void initialize(InfoflowManager manager) {
		// TODO Auto-generated method stub

	}

	@Override
	public Set<Abstraction> getTaintsForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isExclusive(Stmt stmt, Abstraction taintedPath) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<Abstraction> getAliasesForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean supportsCallee(SootMethod method) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean supportsCallee(Stmt callSite) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int getWrapperHits() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public int getWrapperMisses() {
		// TODO Auto-generated method stub
		return 0;
	}

}
