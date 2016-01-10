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
			//������Ҫ�鿴if����Ƿ��й���apֵ�ļ�⣬������������������������ɾ��ap�е�sourceType
			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException))
				checkNullChecker(d1, (IfStmt) stmt, incoming, outgoing, cfg);
			return outgoing;
			//TODO ....
//			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException) &&	//����ap�����˿�ָ��Դ
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
		
		//TODO ���ǵ�Ŀ���Ƕ��ڷ���sinkʱ��accesspath���б�ǣ���Ҫ�����ǻ�֪��ǰ���п�ָ���жϵ�ֵ�����ǵ�incoming��ap��ͬһָ��ġ�
		boolean isSame = isTheSamePart(incoming, checkedValue);
		if(isSame){
			//TODO ����targetExecutePath��outgoing����һ�´���Ҫ��incoming���и��ƣ��޸���sourcetype��Ȼ���滻��outgoing��
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
