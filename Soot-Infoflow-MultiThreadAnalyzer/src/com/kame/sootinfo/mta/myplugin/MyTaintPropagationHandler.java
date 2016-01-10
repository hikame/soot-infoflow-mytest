package com.kame.sootinfo.mta.myplugin;

import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Local;
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
import soot.jimple.infoflow.solver.IMemoryManager;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.kame.SourceSinkType;

public class MyTaintPropagationHandler implements TaintPropagationHandler {

	
	Aliasing aliasing = null;
	private IMemoryManager<Abstraction> memoryManager;
	
	public MyTaintPropagationHandler(Aliasing al) {
		aliasing = al;
	}

	public MyTaintPropagationHandler() {
	}

	@Override
	public Abstraction notifyFlowIn(Unit stmt, Abstraction taint, IInfoflowCFG cfg, FlowFunctionType type) {
//		Map<Stmt, Set<SourceSinkType>> taint.getAccessPath().getSourceTypeReduceMap()
		Map<Stmt, Set<SourceSinkType>> map = taint.getAccessPath().getSourceTypeReduceMapDirectly();
		if(map == null)
			return taint;
if(stmt.toString().startsWith("virtualinvoke freader#4.<java.lang.Object: boolean equals(java.lang.Object)>"))
	stmt.toString();
		Set<SourceSinkType> set = map.get(stmt);
		if(set == null || set.isEmpty())
			return taint;
		AccessPath ap = taint.getAccessPath();
//		ap.getSourceTypes().removeAll(set);
		
//		try {
//			Field field = Abstraction.class.getDeclaredField("accessPath");
//			boolean org = field.isAccessible();
//			field.setAccessible(true);
//			field.set(taint, newAP);
//			field.setAccessible(org);
//			taint = memoryManager.handleMemoryObject(taint);
//		} catch (Exception e) {
//			e.printStackTrace();
//		}
		AccessPath newAP = ap.clone();
		newAP.getSourceTypes().removeAll(set);
		Abstraction result = taint.deriveNewAbstraction(newAP, (Stmt) stmt);
		result = memoryManager.handleGeneratedMemoryObject(taint, result);
//		taint = memoryManager.handleMemoryObject(tmp);
		return result;
	}

	@Override
	public Set<Abstraction> notifyFlowOut(Unit stmt, Abstraction d1, Abstraction incoming, Set<Abstraction> outgoing,
			IInfoflowCFG cfg, FlowFunctionType type) {
		if(type.equals(FlowFunctionType.NormalFlowFunction) && stmt instanceof IfStmt){
			//我们需要查看if语句是否有关于ap值的检测，如有则在其检测成立后续语句中删除ap中的sourceType
			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException))
				checkNullChecker(d1, (IfStmt) stmt, incoming, outgoing, cfg);
			return outgoing;
			//TODO Other checks for other kind of exceptions
		}
		return outgoing;
	}

	private void checkNullChecker(Abstraction d1, IfStmt ifstmt, Abstraction incoming, Set<Abstraction> outgoing, IInfoflowCFG cfg) {
//		
//if(ifstmt.toString().startsWith("if freader#4 == null goto"))
//	ifstmt.toString();
		AccessPath ap = incoming.getAccessPath();
		ConditionExpr condition = (ConditionExpr)ifstmt.getCondition();
		Stmt targetStmt = null;
		if(condition instanceof EqExpr){
			List<Unit> succsUnits = cfg.getSuccsOf(ifstmt);
			int iftPos = succsUnits.indexOf(ifstmt.getTarget());
			targetStmt = (Stmt) succsUnits.get(1 - iftPos);
		}
		else if(condition instanceof NeExpr){
			targetStmt = ifstmt.getTarget();
		}
		else
			return;

		Value op1 = condition.getOp1();
		Value op2 = condition.getOp2();
		Value checkedValue = null;
		Value nullConstant = NullConstant.v();
		if(op1.equals(nullConstant))
			checkedValue = op2;
		else if(op2.equals(nullConstant))
			checkedValue = op1;
		if(checkedValue == null)
			return;
		
		Set<Abstraction> neighbors = incoming.getNeighbors();
		
		//TODO 我们的目标是对于发生sink时的accesspath进行标记，这要求我们获知当前进行空指针判断的值与我们的incoming的ap是同一指向的。
		boolean isSame = isTheSamePart(incoming, checkedValue);
		if(isSame){
			if(outgoing.contains(incoming)){
//				.put(targetStmt, SourceSinkType.NullPointerException);
				Map<Stmt, Set<SourceSinkType>>  map = incoming.getAccessPath().getSourceTypeReduceMap();
				Set<SourceSinkType> set = map.get(targetStmt);
				if(set == null)
					set = new HashSet<SourceSinkType>();
				set.add(SourceSinkType.NullPointerException);
				map.put(targetStmt, set);
			}
		}
		return;
	}

	private boolean isTheSamePart(Abstraction incoming, Value checkedValue) {
		if(incoming.getAccessPath().isLocal() && checkedValue instanceof Local){	//当checked value和Abstraction incoming是同一个local变量
			if(incoming.getAccessPath().getPlainValue().equals(checkedValue))
				return true;
		}
		return false;
	}

	public void generateAliasing(IAliasingStrategy aliasingStrategy, IInfoflowCFG cfg) {
		aliasing = new Aliasing(aliasingStrategy, cfg);
		
	}

	public void setMemoryManager(IMemoryManager<Abstraction> memoryManager) {
		this.memoryManager = memoryManager;
	}
}
