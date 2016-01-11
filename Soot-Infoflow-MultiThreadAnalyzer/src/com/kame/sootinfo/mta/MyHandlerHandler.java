package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.kame.sootinfo.mta.tags.MyMethodTag;

import soot.Body;
import soot.IdentityUnit;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.dexpler.DalvikThrowAnalysis;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JCaughtExceptionRef;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JTrap;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.exceptions.UnitThrowAnalysis;
import soot.util.Chain;
import soot.util.HashChain;

/**
 * @throws Exception */
public class MyHandlerHandler {
	private IInfoflowCFG iCfg;
	
	private Map<Unit, Unit> existingTargets; 	
	JTableSwitchStmt switchTableUnit = null;
	Unit switchTablePreUnit = null;
	List<Value> whats = new ArrayList<Value>();
	List<TrapInfo> newTraps = null; 
	Chain<Trap> orgTraps = null;
	JInstanceFieldRef jifr = null;
	
	CallGraph cg = null;
	SootMethod myHandler = null;
	PatchingChain<Unit> hdMsgUnits = null;
	
	public boolean start(IInfoflowCFG iCfg) throws Exception{
		this.iCfg = iCfg;
		return handleAndroidHandler();
	}
	
	private boolean handleAndroidHandler() throws Exception {
		boolean changed = false;
		SootMethod sendMSG = null;
		sendMSG = Scene.v().getMethod("<android.os.Handler: boolean sendMessage(android.os.Message)>");
		cg = Scene.v().getCallGraph();
		
		Collection<Unit> unitCollection = iCfg.getCallersOf(sendMSG);
		for(Unit callerUnit : unitCollection){	//姣忎釜sendMsg鐨勮皟鐢ㄥ
			reInitFields();
			
			SootMethod callerSM = iCfg.getMethodOf(callerUnit);
			if(Options.v().debug())
				System.out.println("[KM] " + callerSM + "--->" + callerUnit.toString());
			List<ValueBox> useList = callerUnit.getUseBoxes();
			if(useList == null || useList.isEmpty())
				continue;

			Value msgValue = null, hdValue = null;
			InvokeStmt invokeStmt = (InvokeStmt)callerUnit;
			msgValue = invokeStmt.getInvokeExpr().getArg(0);
			hdValue = ((InstanceInvokeExpr)invokeStmt.getInvokeExpr()).getBase();
			
			Integer caseCode = parseCaseCode(callerSM, msgValue, callerUnit); 
			if(caseCode == null)
				break;
			creatMSGHandler(callerUnit, hdValue, caseCode);
			if(myHandler == null){
				System.out.println("[E] Can not creat the replace method for handlerMessage() normally: " + callerUnit);
				continue;
			}
			PatchingChain<Unit> smUnits = callerSM.getActiveBody().getUnits();
			Stmt replaceStmt = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr((Local)hdValue, myHandler.makeRef(), msgValue));
			smUnits.swapWith(callerUnit, replaceStmt);
			
			cg = Scene.v().getCallGraph();
			boolean b = cg.removeAllEdgesOutOf(callerUnit);
			cg.addEdge(new Edge(callerSM, replaceStmt, ((InvokeStmt) replaceStmt).getInvokeExpr().getMethod()));
			
			//闇�瑕佷互鏂板姞鐨勬柟娉昺yhandler[n]涓鸿捣鐐癸紝灏嗗叾鍐呴儴鐨勮皟鐢ㄥ叧绯昏繘琛屽悗缁垎鏋愩��
			changed = true;
		}

		return changed;
	}
	

	private void reInitFields() {
		existingTargets = new HashMap<Unit, Unit>();
		switchTableUnit = null;
		switchTablePreUnit = null;
		newTraps = null;
		whats = new ArrayList<Value>();
		jifr = null;
	}

	private Integer parseCaseCode(SootMethod callerSM, Value msgValue, Unit callerUnit) {
		Body callerBody = callerSM.getActiveBody();
        PatchingChain<Unit> unitsChain = callerBody.getUnits();
        Integer caseCode = null;
        for(Unit u = callerUnit; u != null; u = unitsChain.getPredOf(u)){
        	if(!(u instanceof AssignStmt)){
        		continue;
        	}
        	Value left = ((AssignStmt) u).getLeftOp();
    		Value right = ((AssignStmt) u).getRightOp();
        	if(left.equals(msgValue) && 
        			(right instanceof VirtualInvokeExpr) &&
        			((VirtualInvokeExpr) right).getMethod().equals(
	        				Scene.v().getMethod(
	        						"<android.os.Handler: "
	        						+ "android.os.Message obtainMessage(int)>"))){
        		Value whatValue = ((VirtualInvokeExpr) right).getArgs().get(0);
    			if(!(whatValue instanceof IntConstant)){
    				System.out.println("[E] Message is not get by a constant value: " + u);
    				break;
    			}
    			caseCode = ((IntConstant) whatValue).value;
    			break;
        	}
        	if(left instanceof InstanceFieldRef){
        		InstanceFieldRef ifr = (InstanceFieldRef) left;
        		Value base = ifr.getBase();
        		if(base.equals(msgValue) && ifr.getField().getName().equals("what")){
        			if(!(right instanceof IntConstant)){
        				System.out.println("[E] Message.what is not a constaint value: " + u);
        				break;
        			}
        			caseCode = ((IntConstant) right).value;
        			break;
        		}
        	}
        }
		return caseCode;
	}
	private SootMethod creatMSGHandler(Unit callerUnit, Value hdValue, Integer caseCode) throws Exception {
		//creat handleMSG_[n] and replace the handler.sendMessage(msg) with it in the targetMethod
		SootMethod sendmsgMethod = iCfg.getCalleesOfCallAt(callerUnit).iterator().next();
		Set<Unit> callUnits = iCfg.getCallsFromWithin(sendmsgMethod);
		
		InvokeStmt handleMessageInvoker = null;
		for(Unit u : callUnits){
			if(u instanceof InvokeStmt){
				if(((InvokeStmt) u).getInvokeExpr().getMethod().equals(
						Scene.v().getMethod("<android.os.Handler: "
	        						+ "void handleMessage(android.os.Message)>"))){
					handleMessageInvoker = (InvokeStmt) u;
					break;
				}
			}
		}
		if(handleMessageInvoker == null)
			throw new Exception("Error when find the handleMessage() method in the body of sendMessage()");

		Collection<SootMethod> smCol = iCfg.getCalleesOfCallAt(handleMessageInvoker);
		SootMethod handleMsg = null;
		for(SootMethod sm : smCol){
			if(sm.getDeclaringClass().getSuperclass().equals(Scene.v().getSootClass("android.os.Handler"))
					&& sm.getName().equals("handleMessage")){
				handleMsg = sm;
			}
		}
		if(handleMsg == null)
			throw new Exception("Error when find the handleMessage() method in the body of sendMessage()");

		hdMsgUnits = handleMsg.getActiveBody().getUnits();
		orgTraps = handleMsg.getActiveBody().getTraps();
		if(orgTraps != null && orgTraps.size() > 0){
			newTraps = new ArrayList<TrapInfo>(orgTraps.size());
			for(int i = 0; i < orgTraps.size(); i++)
				newTraps.add(i, null);
		}

		myHandler = new SootMethod(
				"myHandler" + caseCode, 
				Collections.singletonList((Type)RefType.v("android.os.Message")), 
				VoidType.v());
		
		myHandler.addTag(new MyMethodTag(true));
		
		
		handleMsg.getDeclaringClass().addMethod(myHandler);
		
		Body myThinBody = Jimple.v().newBody();
		myThinBody.setMethod(myHandler);
		myHandler.setActiveBody(myThinBody);
		
		for(Local loc : handleMsg.getActiveBody().getLocals())
			myThinBody.getLocals().add(loc);
		
		Local msg = handleMsg.getActiveBody().getParameterLocal(0);
		SootField whatField = ((RefType)msg.getType()).getSootClass().getFieldByName("what");
		jifr = new JInstanceFieldRef(msg, whatField.makeRef());
		
		addUnitsStartFromTarget(hdMsgUnits.getFirst(), true);
		
		if(switchTableUnit == null)
			return null;
		Unit targetUnit = switchTableUnit.getTarget(caseCode - switchTableUnit.getLowIndex());		
		addUnitsStartFromTarget(targetUnit, false);
		
		addTraps();

		return myHandler;
	}
	
	private void addTraps() {
		if(orgTraps == null || orgTraps.isEmpty())
			return;
		Chain<Trap> newTrapChain = new HashChain<Trap>();
		int count = 0;
		for(Trap orgTrap = orgTraps.getFirst(); orgTrap != null; orgTrap = orgTraps.getSuccOf(orgTrap)){
			TrapInfo ti = newTraps.get(count);
			if(ti != null && ti.isValid()){
				if(ti.handlerUnit == null)
					ti.handlerUnit = addUnitsStartFromTarget(orgTrap.getHandlerUnit(), false);
				newTrapChain.add(ti.generateTrap());
			}
			count++;
		}
		
		if(newTrapChain.size() == 0)
			return;
		
		Body handlerBody = myHandler.getActiveBody();
		try {
			java.lang.reflect.Field tcField = Body.class.getDeclaredField("trapChain");
			boolean ac = tcField.isAccessible();
			tcField.setAccessible(true);
			tcField.set(handlerBody, newTrapChain);
			tcField.setAccessible(ac);
		} catch (Exception e) {
			e.printStackTrace();
		} 
	}

	/**it will append the codes starting from startUnit and end with null or goto stmt
	 * the the return value is the new unit in the created method.
	 * @param searchForSwitchTable */
	private Unit addUnitsStartFromTarget(Unit startUnit, boolean searchForSwitchTable) {
		if(existingTargets.containsKey(startUnit) && existingTargets.get(startUnit) != null)	
			return (Unit) existingTargets.get(startUnit);
		
		//在后续节点的添加过程中，可能会将本代码段终点的goto语句的跳转目标添加进去，因此我们要先进行一次记录
		//毕竟，我们的goto目标可能也是其他代码段的中间代码
		//如以下代码的最后一句：
		//if(msg.obj != null)
		//	msg.obj.equals("");
		//else
		//	msg.obj.equals("1");
		//msg.obj.equals("2");
		GotoStmt gotoStmt = null;
		for(Unit u = startUnit; u != null; u = hdMsgUnits.getSuccOf(u)){
			if(u instanceof GotoStmt){
				gotoStmt = (GotoStmt) u;
				existingTargets.put(gotoStmt.getTarget(), null);
				break;
			}
			if(u instanceof ReturnVoidStmt)
				break;
		}
		
		Unit result = null;
		Unit preUnit = null;
		if(switchTableUnit != null && switchTableUnit.getTargets().contains(startUnit))
			preUnit = switchTablePreUnit;
		for(Unit u = startUnit; u != null; u = hdMsgUnits.getSuccOf(u)){
			if(existingTargets.containsKey(u) && existingTargets.get(u) != null){	//exception处理代码并不会有return语句，而其后面的代码有可能已经被加入进去过了~
				break;	//此处不必担心是代码段的第一句，因为这种情况在本方法开头处已经处理了。
			}
			preUnit = addOneUnit(u, searchForSwitchTable, preUnit);
			if(u.equals(startUnit)){
				result = preUnit;
				existingTargets.put(startUnit, result);
			}
			if(existingTargets.containsKey(u) && existingTargets.get(u) == null)
				existingTargets.put(u, preUnit);
			if(searchForSwitchTable && switchTableUnit != null && u.equals(switchTableUnit))	//当u就是我们的目标SwitchTable时
				break;
			if((u instanceof GotoStmt) || (u instanceof ReturnVoidStmt))
				break;
		}

		return result;
	}

	private Unit addOneUnit(Unit u, boolean searchForSwitchTable, Unit preUnit) {
		Unit newUnit = (Unit) u.clone();
		PatchingChain<Unit> unitsChain = myHandler.getActiveBody().getUnits(); 	
		if(u instanceof InvokeStmt){	//当时方法调用语句时，对call graph进行处理
			InvokeExpr invokeExpr = ((InvokeStmt) u).getInvokeExpr();
			modifyCallGraph(invokeExpr, newUnit);
		}
		else if(u instanceof AssignStmt){
			Value rightValue = ((AssignStmt) u).getRightOp();
			if(rightValue.toString().equals(jifr.toString()))
				whats.add(((AssignStmt)u).getLeftOp());
			if(rightValue instanceof InvokeExpr){
				InvokeExpr invokeExpr = (InvokeExpr) rightValue;
				modifyCallGraph(invokeExpr, newUnit);
			}
		}
		else if(u instanceof GotoStmt){		
			Unit target = ((GotoStmt) u).getTarget();
			Unit newTarget = addUnitsStartFromTarget(target, searchForSwitchTable);
			((GotoStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof IfStmt){
			Unit target = ((IfStmt) u).getTarget();
			Unit newTarget = addUnitsStartFromTarget(target, searchForSwitchTable);
			((IfStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof TableSwitchStmt){
			TableSwitchStmt uu = (TableSwitchStmt) u;
			if(searchForSwitchTable && whats.contains(((TableSwitchStmt)u).getKey())){
				switchTableUnit = (JTableSwitchStmt) u;
				newUnit = new JNopStmt();
				switchTablePreUnit = newUnit;
			}
			else for(int i = uu.getLowIndex(); i <= uu.getHighIndex(); i++){
				Unit target = uu.getTarget(i);
				Unit newTarget = addUnitsStartFromTarget(target, searchForSwitchTable);
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
		Edge newEdge = new Edge(myHandler, newUnit, tgt, kind);
		cg.addEdge(newEdge);
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
		TrapInfo ti = newTraps.get(count);
		if(ti == null){
			ti = new TrapInfo();
			ti.exception = trap.getException();
			newTraps.set(count, ti);
		}
		return ti;
	}

	private class TrapInfo{
	    /** The exception being caught. */
	    private transient SootClass exception;

	    /** The first unit being trapped. */
	    private Unit beginUnit;

	    /** The unit just before the last unit being trapped. */
	    private Unit endUnit;

	    /** The unit to which execution flows after the caught exception is triggered. */
	    private Unit handlerUnit;

		public boolean isValid() {
			boolean result = (exception != null) && (beginUnit != null) && (endUnit != null);
			return result;
		}

		public Trap generateTrap() {
			return new JTrap(exception, beginUnit, endUnit, handlerUnit);
		}
	}
}