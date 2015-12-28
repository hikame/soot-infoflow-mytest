package com.kame.sootinfo.mta.myplugin;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;;

public class MyTaintWrapper implements ITaintPropagationWrapper {
	EasyTaintWrapper etw;

	public MyTaintWrapper(){
		try {
			etw = new EasyTaintWrapper(new File("EasyTaintWrapperSource.txt"));
		} catch (IOException e) {
			e.printStackTrace();
			etw = null;
		}
	}
	
	@Override
	public void initialize(InfoflowManager manager) {
		// TODO Auto-generated method stub
		etw.initialize(manager);
	}

	@Override
	public Set<Abstraction> getTaintsForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		return etw.getTaintsForMethod(stmt, d1, taintedPath);
	}

	@Override
	public boolean isExclusive(Stmt stmt, Abstraction taintedPath) {
		// TODO Auto-generated method stub
		return etw.isExclusive(stmt, taintedPath);
	}

	@Override
	public Set<Abstraction> getAliasesForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		return etw.getAliasesForMethod(stmt, d1, taintedPath);
	}

	@Override
	public boolean supportsCallee(SootMethod method) {
		// TODO Auto-generated method stub
		return etw.supportsCallee(method);
	}

	@Override
	public boolean supportsCallee(Stmt callSite) {
		// TODO Auto-generated method stub
		return etw.supportsCallee(callSite);
	}

	@Override
	public int getWrapperHits() {
		// TODO Auto-generated method stub
		return etw.getWrapperHits();
	}

	@Override
	public int getWrapperMisses() {
		// TODO Auto-generated method stub
		return etw.getWrapperHits();
	}

}
