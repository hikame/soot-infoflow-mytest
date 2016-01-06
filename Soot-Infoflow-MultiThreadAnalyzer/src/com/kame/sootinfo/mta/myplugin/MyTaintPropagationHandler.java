package com.kame.sootinfo.mta.myplugin;

import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AbstractionAtSink;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.problems.InfoflowProblem;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;

public class MyTaintPropagationHandler implements TaintPropagationHandler {
	MySourceSinkManager ssm;
//	InfoflowProblem forwardProblem;
	
	public MyTaintPropagationHandler(ISourceSinkManager ssm) {
		this.ssm = (MySourceSinkManager) ssm;
	}

//	public void setInfoflowProblem(InfoflowProblem fp){
//		this.forwardProblem = fp;
//	}
	
	@Override
	public void notifyFlowIn(Unit stmt, Abstraction taint, IInfoflowCFG cfg, FlowFunctionType type) {
		// TODO Auto-generated method stub

	}

	@Override
	public Set<Abstraction> notifyFlowOut(Unit stmt, Abstraction d1, Abstraction incoming, Set<Abstraction> outgoing,
			IInfoflowCFG cfg, FlowFunctionType type) {
////!!!!!!!!!!!!!!此路不通！！！！
//		if(!type.equals(FlowFunctionType.NormalFlowFunction))
//			return outgoing;
//		
//		if(!incoming.isAbstractionActive() || incoming.isImplicit())	
//			return outgoing;
//		
//		AccessPath ap = incoming.getAccessPath();
//		
//		for(ValueBox box : stmt.getUseBoxes()){
//			Value val = box.getValue();
//			if(val instanceof InstanceFieldRef)
//				if(ap != null && ssm.checkInstanceFieldRefAsSink(val, ap)){
////					if(forwardProblem != null)
////						forwardProblem.getResults().add(new AbstractionAtSink(incoming, (Stmt) stmt));
//					return outgoing;
//				}
//		}
//		
		return outgoing;
	}
}
