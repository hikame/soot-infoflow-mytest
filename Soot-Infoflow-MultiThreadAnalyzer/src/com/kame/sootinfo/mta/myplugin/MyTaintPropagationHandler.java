package com.kame.sootinfo.mta.myplugin;

import java.util.List;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ConditionExpr;
import soot.jimple.EqExpr;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.NeExpr;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.infoflow.aliasing.AbstractBulkAliasStrategy;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.aliasing.IAliasingStrategy;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AbstractionAtSink;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.problems.InfoflowProblem;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.kame.SourceSinkType;

public class MyTaintPropagationHandler implements TaintPropagationHandler {

	
	Aliasing aliasing = null;
	
	public MyTaintPropagationHandler(Aliasing al) {
		aliasing = al;
	}

	public MyTaintPropagationHandler() {
	}

	@Override
	public void notifyFlowIn(Unit stmt, Abstraction taint, IInfoflowCFG cfg, FlowFunctionType type) {
		// TODO Auto-generated method stub

	}

	@Override
	public Set<Abstraction> notifyFlowOut(Unit stmt, Abstraction d1, Abstraction incoming, Set<Abstraction> outgoing,
			IInfoflowCFG cfg, FlowFunctionType type) {
		if(type.equals(FlowFunctionType.NormalFlowFunction) && stmt instanceof IfStmt){
			//我们需要查看if语句是否有关于ap值的检测，如有则在其检测成立后续语句中删除ap中的sourceType
			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException))
				checkNullChecker(d1, (IfStmt) stmt, incoming, outgoing, cfg);
			return outgoing;
			//TODO ....
//			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException) &&	//传入ap包含了空指针源
//					ifstmt.get)
		}
		return outgoing;
	}

	private void checkNullChecker(Abstraction d1, IfStmt ifstmt, Abstraction incoming, Set<Abstraction> outgoing, IInfoflowCFG cfg) {
		AccessPath ap = incoming.getAccessPath();
		if(ap.getFieldCount() > 0)
			return;
		ConditionExpr condition = (ConditionExpr)ifstmt.getCondition();
		Stmt targetExecutePath = null;
		if(condition instanceof EqExpr){
			List<Unit> succsUnits = cfg.getSuccsOf(ifstmt);
			int iftPos = succsUnits.indexOf(ifstmt.getTarget());
			targetExecutePath = (Stmt) succsUnits.get(1 - iftPos);
		}
		else if(condition instanceof NeExpr){
			targetExecutePath = ifstmt.getTarget();
		}
		else
			return;

		Value op1 = condition.getOp1();
		Value op2 = condition.getOp2();
		Value checkedValue = null;
		Value nullConstant = NullConstant.v();
//		Set<Abstraction> neighbors = null;
		
		if(op1.equals(nullConstant))
			checkedValue = op2;
		else if(op2.equals(nullConstant))
			checkedValue = op1;
		
		if(checkedValue == null)
			return;
		
		//TODO 我们的目标是对于发生sink时的accesspath进行标记，这要求我们获知当前进行空指针判断的值与我们的incoming的ap是同一指向的。
		boolean isSame = isTheSamePart(incoming, checkedValue);
		if(isSame){
			//TODO 对于targetExecutePath的outgoing进行一下处理，要将incoming进行复制，修改其sourcetype，然后替换到outgoing中
		}
	}

	private boolean isTheSamePart(Abstraction incoming, Value checkedValue) {
		// TODO Auto-generated method stub
		return false;
	}

	public void generateAliasing(IAliasingStrategy aliasingStrategy, IInfoflowCFG cfg) {
		aliasing = new Aliasing(aliasingStrategy, cfg);
		
	}
}
