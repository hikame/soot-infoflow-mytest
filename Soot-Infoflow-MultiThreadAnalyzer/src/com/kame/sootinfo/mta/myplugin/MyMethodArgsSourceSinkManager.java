package com.kame.sootinfo.mta.myplugin;

import heros.InterproceduralCFG;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;

//Created by KAME, 20151111

public class MyMethodArgsSourceSinkManager implements ISourceSinkManager {
	boolean taintSubFields = true;
	String targetMethods = null; 
	String sinks = null;
//	private static final String sinkAP = "<soot.jimple.infoflow.test.SourceSinkTestCode: void doleakSecret2(soot.jimple.infoflow.test.SourceSinkTestCode$A)>";
//	protected static final String sink = "<soot.jimple.infoflow.test.android.ConnectionManager: void publish(java.lang.String)>";
	
	/**
	 * @param taintSubFields
	 * 用于设定TaintAccess中taintSubFields的值。
	 * @param targetMethods
	 * 给出的方法名的参数是污点值
	 * @param sinks
	 * 给出的方法名是sink*/
	public MyMethodArgsSourceSinkManager(boolean taintSubFields, String targetMethods, String sinks){
		this.taintSubFields =  taintSubFields;
		this.targetMethods = targetMethods;
		this.sinks = sinks;
	}
	
	@Override
	public SourceInfo getSourceInfo(Stmt sCallSite,
			InterproceduralCFG<Unit, SootMethod> cfg) {
//参照jimple的格式，方法的参数在方法的实现代码中是通过左操作数为临时操作变量，右操作数为实参的形式进行表示的，这种情况下，为左操作数创建TaintedPath信息。
		if(!cfg.getMethodOf(sCallSite).toString().equals(targetMethods))
			return null;
		if(!(sCallSite instanceof DefinitionStmt))
			return null;
		DefinitionStmt ds = (DefinitionStmt) sCallSite;
		if(!(ds.getRightOp() instanceof ParameterRef))
			return null;
		AccessPath ap = AccessPathFactory.v().createAccessPath(
				((DefinitionStmt) sCallSite).getLeftOp(), taintSubFields);
//System.out.println("[TSrc-" + id + "] [!] This is a source! AP: " + ap);
		return new SourceInfo(ap);
	}

	@Override
	public boolean isSink(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg,
			AccessPath ap) {
//long id = Thread.currentThread().getId();
//System.out.println("[TSink-" + id + "] Method: " + cfg.getMethodOf(sCallSite));
//System.out.println("[TSink-" + id + "] Stmt:" + sCallSite);
		if (!sCallSite.containsInvokeExpr())
			return false;
		SootMethod target = sCallSite.getInvokeExpr().getMethod();
		
		if(target.toString().contains("equal"))
			System.out.println();
		
		if ((target.getSignature().equals(sinks))
				&& sCallSite.getInvokeExpr().getArgCount() > 0) {
			if (ap == null){
//System.out.println("[TSink-" + id + "] [!] This is a sink! AP: " + ap);
				return true;
			}
			else if (ap.getPlainValue() == sCallSite.getInvokeExpr().getArg(0))	//!!!此处需要配置！
				if (ap.isLocal() || ap.getTaintSubFields()){
//System.out.println("[TSink-" + id + "] [!] This is a sink! AP: " + ap);
					return true;
				}
		}
		
		else if(sCallSite instanceof InstanceInvokeExpr){
			Value base = ((InstanceInvokeExpr) sCallSite).getBase();
			Local local = ap.getPlainValue();
			if(base.equals(local))
				System.out.println();
		}
		return false;
	}

}
