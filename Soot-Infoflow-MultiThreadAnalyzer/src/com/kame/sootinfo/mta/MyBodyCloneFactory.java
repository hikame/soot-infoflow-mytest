package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.IdentityUnit;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.Scene;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.SwitchStmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JNopStmt;
import soot.jimple.toolkits.callgraph.Edge;
import soot.util.Chain;
import soot.util.HashChain;
/**body.importBodyContentsFrom(orgbody) totally workable*/
public class MyBodyCloneFactory {
	IInfoflowCFG iCfg = ControlFlowGraphManager.v().getInfoflowCFG();
	
	/**Original body unit -> New body unit*/
	Map<Unit, Unit> multiProdsUnits = new HashMap<Unit, Unit>(); 	
	List<TrapInfo> newTrapInfos = new ArrayList<TrapInfo>(); 
	Chain<Trap> orgTraps = null;
	
	private Body newBody = null;
	private Body orgBody = null;
	private List<Local> newLocals = null;
	private List<Local> orgLocals = null;
	
	Unit substituteOfStop = null;
	public Unit getSubstituteOfStop(){
		return substituteOfStop;
	}
	
	/***/
	public MyBodyCloneFactory(Body newbody, Body orgbody) {
		this.orgBody = orgbody;
		for(Unit u : orgBody.getUnits())
			if(iCfg.getPredsOf(u).size() > 1)
				multiProdsUnits.put(u, null);
		orgTraps = orgBody.getTraps();
		for(int i = 0; i < orgTraps.size(); i++)
			newTrapInfos.add(i, null);
		
		if(newbody == null){
			if(newBody == null){	//assert startUnit == null???
				newBody = Jimple.v().newBody();
				for(Local loc : orgBody.getLocals())
					newBody.getLocals().add(Jimple.v().newLocal(loc.getName(), loc.getType()));
//				loc.clone();
			}
		}
		else 
			this.newBody = newbody;
		
		newLocals = new ArrayList<Local>(newBody.getLocals());
		orgLocals = new ArrayList<Local>(orgBody.getLocals());
		return;
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
	public Unit addUnits(Unit preUnit, Unit startUnit, Unit stopUnit) {
		substituteOfStop = null;
		if(multiProdsUnits.containsKey(startUnit) && multiProdsUnits.get(startUnit) != null)	
			return (Unit) multiProdsUnits.get(startUnit);
		
		Unit result = null;
		for(Unit u = startUnit; u != null; u = orgBody.getUnits().getSuccOf(u)){
			if(multiProdsUnits.containsKey(u) && multiProdsUnits.get(u) != null){
				break;	//no worry about the head of this method
			}
			preUnit = addOneUnit(preUnit, u, stopUnit);
			if(u.equals(stopUnit))	//we need to add the stopUnit into the newBody with a substitute of Nop statement. and then check if it is the stop Unit
				break;
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
		PatchingChain<Unit> unitsChain = newBody.getUnits();
		if(u.equals(stopUnit)){
			newUnit = new JNopStmt();	//we replace stopUnit with substituteofstop(a nop stmt)
			substituteOfStop = newUnit;
		}
		else if(u instanceof InvokeStmt){	//take care of call graph
			InvokeExpr invokeExpr = ((InvokeStmt) u).getInvokeExpr();
			modifyCallGraph(invokeExpr, newUnit);
		}
		else if(u instanceof DefinitionStmt){
			Value rightValue = ((DefinitionStmt) u).getRightOp();
			ValueBox leftBox = ((DefinitionStmt) u).getLeftOpBox();
//			if(rightValue.toString().equals(jifr.toString()))
//				whats.add(((AssignStmt)u).getLeftOp());
			if(rightValue instanceof InvokeExpr){
				InvokeExpr invokeExpr = (InvokeExpr) rightValue;
				modifyCallGraph(invokeExpr, newUnit);
			}
		}
		else if(u instanceof GotoStmt){		
			Unit target = ((GotoStmt) u).getTarget();
			Unit newTarget = addUnits(null, target, stopUnit);
			((GotoStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof IfStmt){
			Unit target = ((IfStmt) u).getTarget();
			Unit newTarget = addUnits(null, target, stopUnit);
			((IfStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof SwitchStmt){
			SwitchStmt swtStmt= (SwitchStmt) u;
			List<Unit> targets = swtStmt.getTargets();
			if(swtStmt instanceof TableSwitchStmt){
				TableSwitchStmt tss = (TableSwitchStmt) swtStmt;
				for(int i = tss.getLowIndex(); i <= tss.getHighIndex(); i++){
					Unit target = targets.get(i);
					Unit newTarget = addUnits(null, target, stopUnit);
					((TableSwitchStmt) newUnit).setTarget(i, newTarget);
				}
			}
			else if(swtStmt instanceof LookupSwitchStmt){
				int count = 0;
				for(IntConstant luValue : ((LookupSwitchStmt)swtStmt).getLookupValues()){
					Unit target = targets.get(count);
					Unit newTarget = addUnits(null, target, stopUnit);
					((LookupSwitchStmt) newUnit).setTarget(count, newTarget);
					((LookupSwitchStmt) newUnit).setLookupValue(count, luValue.value);
					count++;
				}
			}
		}	
		
		int index = 0;
		if(!u.equals(stopUnit))	//handling the local uses.
			for(ValueBox box : u.getUseAndDefBoxes()){
				if(box.getValue() instanceof Local){
					Local newL = newLocals.get(orgLocals.indexOf(box.getValue()));
					newUnit.getUseAndDefBoxes().get(index).setValue(newL);
				}
				index++;
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
		int index = 0;
		for(Trap trap : orgTraps){
			if(trap.getBeginUnit().equals(u))
				getTrapInfoAt(index, trap).beginUnit = newUnit;
			if(trap.getEndUnit().equals(u))
				getTrapInfoAt(index, trap).endUnit = newUnit;
			if(trap.getHandlerUnit().equals(u))
				getTrapInfoAt(index, trap).handlerUnit = newUnit;
			index++;
		}
	}

	private TrapInfo getTrapInfoAt(int index, Trap trap) {
		TrapInfo ti = newTrapInfos.get(index);
		if(ti == null){
			ti = new TrapInfo();
			ti.exception = trap.getException();
			newTrapInfos.set(index, ti);
		}
		return ti;
	}
	
	public void completeNewTraps(){
		if(orgTraps == null || orgTraps.isEmpty())
			return;
		Chain<Trap> newTrapChain = new HashChain<Trap>();
		int count = 0;
		for(Trap orgTrap = orgTraps.getFirst(); orgTrap != null; orgTrap = orgTraps.getSuccOf(orgTrap)){
			TrapInfo ti = newTrapInfos.get(count);
			if(ti != null && ti.isValid()){
				if(ti.handlerUnit == null)
					ti.handlerUnit = addUnits(null, orgTrap.getHandlerUnit(), null);
				newTrapChain.add(ti.generateTrap());
			}
			count++;
		}
		
		if(newTrapChain.size() == 0)
			return;
		
		try {
			java.lang.reflect.Field tcField = Body.class.getDeclaredField("trapChain");
			boolean ac = tcField.isAccessible();
			tcField.setAccessible(true);
			tcField.set(newBody, newTrapChain);
			tcField.setAccessible(ac);
		} catch (Exception e) {
			throw new RuntimeException(e);
		} 
	}

	public Body getNewBody() {
		return newBody;
	}
}
