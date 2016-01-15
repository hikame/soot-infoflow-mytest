package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.Scene;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.TableSwitchStmt;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JNopStmt;
import soot.jimple.toolkits.callgraph.Edge;
import soot.util.Chain;
/**body.importBodyContentsFrom(orgbody) totally workable*/
public class MyBodyCloneFactory {
	IInfoflowCFG iCfg = ControlFlowGraphManager.v().getInfoflowCFG();
	
	/**Original body unit -> New body unit*/
	Map<Unit, Unit> multiProdsUnits = new HashMap<Unit, Unit>(); 	
	List<TrapInfo> newTrapInfos = new ArrayList<TrapInfo>(); 
	Chain<Trap> orgTraps = null;
	
	Body newBody = null;
	Body orgBody = null;
	
	Unit substituteOfStop = null;
	public Unit getSubstituteOfStop(){
		return substituteOfStop;
	}
	
	/***/
	public MyBodyCloneFactory(Body newbody, Body orgbody) {
//		newbody.importBodyContentsFrom(orgbody);
		if(newbody == null){
			if(orgBody == null){	//assert startUnit == null???
				orgBody = Jimple.v().newBody();
				for(Local loc : orgBody.getLocals())
					newBody.getLocals().add(loc);
			}
		}
		else 
			this.newBody = newbody;
		
		this.orgBody = orgbody;
		for(Unit u : orgBody.getUnits())
			if(iCfg.getPredsOf(u).size() > 1)
				multiProdsUnits.put(u, null);
		orgTraps = orgBody.getTraps();
	}
	
	/**
	 * @param startUnit start unit in orgBody. if it is null, will added from the start.
	 * @param stopUnit stop unit in orgBody. if it is null, all will be added.*/
	public Body copy(Unit startUnit, Unit stopUnit){
		addUnits(null, startUnit, stopUnit);
		return newBody;
	}
	/**
	 * @param preUnit the preceding unit where the copy of startUnit should be inserted in newBody.
	 * @param stopUnit stop uni in orgBody. If the cloning process come to this unit, the process will stop.
	 * @return the copy of startUnit in newBody.
	 **/
	private Unit addUnits(Unit preUnit, Unit startUnit, Unit stopUnit) {
		if(multiProdsUnits.containsKey(startUnit) && multiProdsUnits.get(startUnit) != null)	
			return (Unit) multiProdsUnits.get(startUnit);
		
		Unit result = null;
		for(Unit u = startUnit; u != null; u = orgBody.getUnits().getSuccOf(u)){
			if(multiProdsUnits.containsKey(u) && multiProdsUnits.get(u) != null){	//exception处理代码并不会有return语句，而其后面的代码有可能已经被加入进去过了~
				break;	//此处不必担心是代码段的第一句，因为这种情况在本方法开头处已经处理了。
			}
			if(u.equals(stopUnit))
				break;
			preUnit = addOneUnit(preUnit, u, stopUnit);
			if(u.equals(startUnit))
				result = preUnit;
			if(multiProdsUnits.containsKey(u) && multiProdsUnits.get(u) == null)
				multiProdsUnits.put(u, preUnit);
			if((u instanceof GotoStmt) || iCfg.isExitStmt(u))
				break;
		}		
		return result;
	}

	private Unit addOneUnit( Unit preUnit, Unit u, Unit stopUnit) {
		Unit newUnit = (Unit) u.clone();
		PatchingChain<Unit> unitsChain = orgBody.getUnits(); 	
		if(u instanceof InvokeStmt){	//当时方法调用语句时，对call graph进行处理
			InvokeExpr invokeExpr = ((InvokeStmt) u).getInvokeExpr();
			modifyCallGraph(invokeExpr, newUnit);
		}
		else if(u instanceof AssignStmt){
			Value rightValue = ((AssignStmt) u).getRightOp();
//			if(rightValue.toString().equals(jifr.toString()))
//				whats.add(((AssignStmt)u).getLeftOp());
			if(rightValue instanceof InvokeExpr){
				InvokeExpr invokeExpr = (InvokeExpr) rightValue;
				modifyCallGraph(invokeExpr, newUnit);
			}
		}
		else if(u instanceof GotoStmt){		
			Unit target = ((GotoStmt) u).getTarget();
			Unit newTarget = addUnits(target, null, stopUnit);
			((GotoStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof IfStmt){
			Unit target = ((IfStmt) u).getTarget();
			Unit newTarget = addUnits(target, null, stopUnit);
			((IfStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof TableSwitchStmt){
			TableSwitchStmt uu = (TableSwitchStmt) u;	//新的方案下我们的目标switchUnit在这一步被直接添加nop语句
			if(u.equals(stopUnit)){
				newUnit = new JNopStmt();
				substituteOfStop = newUnit;
			}
			else for(int i = uu.getLowIndex(); i <= uu.getHighIndex(); i++){
				Unit target = uu.getTarget(i);
				Unit newTarget = addUnits(target, null, stopUnit);
				((TableSwitchStmt) newUnit).setTarget(i, newTarget);
			}
		}	
		if(preUnit == null)
			unitsChain.add(newUnit);
		else
			unitsChain.insertAfter(newUnit, preUnit);
		
		checkForTraps(u, newUnit);
		return newUnit;
	}
	
	private void modifyCallGraph(InvokeExpr invokeExpr, Unit newUnit) {
		SootMethod tgt = invokeExpr.getMethod();
		Kind kind = Edge.ieToKind(invokeExpr);
		Edge newEdge = new Edge(newBody.getMethod(), newUnit, tgt, kind);
		Scene.v().getCallGraph().addEdge(newEdge);
	}

	private void checkForTraps(Unit u, Unit newUnit) {
		int count = 0;
		for(Trap trap : orgTraps){
			if(trap.getBeginUnit().equals(u))
				getTrapInfoAt(count, trap).beginUnit = newUnit;
			if(trap.getEndUnit().equals(u))
				getTrapInfoAt(count, trap).endUnit = newUnit;
			if(trap.getHandlerUnit().equals(u))
				getTrapInfoAt(count, trap).handlerUnit = newUnit;
			count++;
		}
	}

	private TrapInfo getTrapInfoAt(int count, Trap trap) {
		TrapInfo ti = newTrapInfos.get(count);
		if(ti == null){
			ti = new TrapInfo();
			ti.exception = trap.getException();
			newTrapInfos.set(count, ti);
		}
		return ti;
	}
}
