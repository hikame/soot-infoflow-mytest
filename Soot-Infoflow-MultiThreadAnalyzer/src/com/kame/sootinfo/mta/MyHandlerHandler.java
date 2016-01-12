package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.kame.sootinfo.mta.tags.MyMethodTag;

import soot.Body;
import soot.IdentityUnit;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.PrimType;
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
import soot.dexpler.typing.UntypedIntOrFloatConstant;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.AbstractInstanceInvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JCaughtExceptionRef;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JTrap;
import soot.jimple.internal.JVirtualInvokeExpr;
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
	IInfoflowCFG iCfg;
	Map<Unit, Unit> existingUnits; 	
//	List<Value> whats = new ArrayList<Value>();
	List<TrapInfo> newMethodTraps = null; 
	Chain<Trap> orgMethodTraps = null;
//	JInstanceFieldRef jifr = null;
	
	CallGraph cg = null;
	SootMethod myHandler = null;
	PatchingChain<Unit> targetMethodUnits = null;
	Unit substituteForSwitch = null;
	
//	SootMethod switchContainer = null;
	Stmt switchContainerInvoker = null;
//	int keyParamIndex = -1;
	
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
		for(Unit sendMsgInvoker : unitCollection){	
			reInitFields();
			
			SootMethod sendMsgContainerMethod = iCfg.getMethodOf(sendMsgInvoker);
			if(Options.v().debug())
				System.out.println("[KM] " + sendMsgContainerMethod + "--->" + sendMsgInvoker.toString());
//			List<ValueBox> useList = callerUnit.getUseBoxes();
//			if(useList == null || useList.isEmpty())
//				continue;

			Value msgValue = null, hdValue = null;
			InvokeStmt invokeStmt = (InvokeStmt)sendMsgInvoker;
			msgValue = invokeStmt.getInvokeExpr().getArg(0);
			hdValue = ((InstanceInvokeExpr)invokeStmt.getInvokeExpr()).getBase();
			
			Integer caseCode = parseCaseCode(sendMsgContainerMethod, msgValue, sendMsgInvoker); 
			if(caseCode == null)
				break;
			
			SootMethod handleMsgMethod = getHandleMsgMethod(sendMsgInvoker);
			JTableSwitchStmt switchUnit = (JTableSwitchStmt) searchForSwitchCode(handleMsgMethod, handleMsgMethod.getActiveBody().getParameterLocal(0), 0);	//handleMsgMethod的参数只有一个撒~
			if(switchUnit == null)
				//TODO record:switchUnit == null
				continue;
			
			SootMethod myHandler = creatMSGHandler(switchUnit, caseCode);
			assert myHandler != null;
			
			Stmt replaceStmt = generateReplaceStmt();
			SootMethod sm = iCfg.getMethodOf(switchContainerInvoker);
			sm.getActiveBody().getUnits().swapWith(switchContainerInvoker, replaceStmt);
			cg = Scene.v().getCallGraph();
			boolean b = cg.removeAllEdgesOutOf(switchContainerInvoker);
			cg.addEdge(new Edge(sm, replaceStmt, myHandler));
			changed = true;
		}

		return changed;
	}
	

	private Stmt generateReplaceStmt() {
		InvokeExpr invExpr = switchContainerInvoker.getInvokeExpr();
		List<Value> actualArgs = invExpr.getArgs();
		SootMethod switchContainer = invExpr.getMethod();
		
		InvokeExpr newInvExpr = null;
		if(invExpr instanceof InstanceInvokeExpr){
			Value base = ((InstanceInvokeExpr) invExpr).getBase();
			if(invExpr instanceof InterfaceInvokeExpr)
				newInvExpr = new JInterfaceInvokeExpr(base, myHandler.makeRef(), actualArgs);
			else if (invExpr instanceof SpecialInvokeExpr)
				newInvExpr = new JSpecialInvokeExpr((Local) base, myHandler.makeRef(), actualArgs);
			else if (invExpr instanceof VirtualInvokeExpr)
				newInvExpr = new JVirtualInvokeExpr(base, myHandler.makeRef(), actualArgs);
		}
		else if(invExpr instanceof StaticInvokeExpr){
			newInvExpr = new JStaticInvokeExpr(myHandler.makeRef(), actualArgs);
		}
		else{
			throw new RuntimeException("switchContainerInvoker is neighter instance invoke or static invoke.");
		}
		Stmt replacementStmt = null;
		if(switchContainerInvoker instanceof AssignStmt){
			Value left = ((AssignStmt)switchContainerInvoker).getLeftOp();
			replacementStmt = new JAssignStmt(left, newInvExpr);
		}else if(switchContainerInvoker instanceof InvokeStmt){
			replacementStmt = new JInvokeStmt(newInvExpr);
		}else{
			throw new RuntimeException("switchContainerInvoker is neighter InvokeStmt or AssignStmt.");
		}
		return replacementStmt;
	}

	private SootMethod getHandleMsgMethod(Unit sendMsgInvoker) {
		assert iCfg.getCalleesOfCallAt(sendMsgInvoker).size() == 1;	//正常情况下一个invoke stmt只有一个调用对象
		SootMethod sendmsgMethod = iCfg.getCalleesOfCallAt(sendMsgInvoker).iterator().next();
		assert iCfg.getCallsFromWithin(sendmsgMethod).size() == 1;	//我们之前对于sendMsg方法进行了修改，该方法中唯一的调用就是想用的handleMsg方法
		Unit handlerMsgInvoker = iCfg.getCallsFromWithin(sendmsgMethod).iterator().next();
		assert iCfg.getCalleesOfCallAt(handlerMsgInvoker).size() == 1;	//正常情况下一个invoke stmt只有一个调用对象
		SootMethod handleMsg = iCfg.getCalleesOfCallAt(handlerMsgInvoker).iterator().next();
		assert handleMsg != null;
//		switchContainer = handleMsg;
//		keyParamIndex = 0;
		switchContainerInvoker = (Stmt) handlerMsgInvoker;

		return handleMsg;
	}

	private void reInitFields() {
		existingUnits = new HashMap<Unit, Unit>();
//		switchTableUnit = null;
//		switchTablePreUnit = null;
		newMethodTraps = null;
//		whats = new ArrayList<Value>();
//		jifr = null;
		substituteForSwitch = null;
//		switchContainer = null;
//		keyParamIndex = -1;
		switchContainerInvoker = null;
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
	private SootMethod creatMSGHandler(JTableSwitchStmt switchUnit, Integer caseCode) throws Exception {
		SootMethod targetMethod = iCfg.getMethodOf(switchUnit); 
		targetMethodUnits = targetMethod.getActiveBody().getUnits();
		orgMethodTraps = targetMethod.getActiveBody().getTraps();
		if(orgMethodTraps != null && orgMethodTraps.size() > 0){
			newMethodTraps = new ArrayList<TrapInfo>(orgMethodTraps.size());
			for(int i = 0; i < orgMethodTraps.size(); i++)
				newMethodTraps.add(i, null);
		}

		myHandler = new SootMethod(
				"myHandler" + caseCode, 
				targetMethod.getParameterTypes(), 
				targetMethod.getReturnType());
		
		myHandler.addTag(new MyMethodTag(true));
		targetMethod.getDeclaringClass().addMethod(myHandler);
		
		Body myThinBody = Jimple.v().newBody();
		myThinBody.setMethod(myHandler);
		myHandler.setActiveBody(myThinBody);
		
		for(Local loc : targetMethod.getActiveBody().getLocals())
			myThinBody.getLocals().add(loc);
		
//		Local msg = targetMethod.getActiveBody().getParameterLocal(0);
//		SootField whatField = ((RefType)msg.getType()).getSootClass().getFieldByName("what");
//		jifr = new JInstanceFieldRef(msg, whatField.makeRef());
		
		addUnitsStartFromTarget(targetMethodUnits.getFirst(), null, switchUnit);
		Unit targetUnit = switchUnit.getTarget(caseCode - switchUnit.getLowIndex());		
		addUnitsStartFromTarget(targetUnit, substituteForSwitch, null);
		addTraps();

		return myHandler;
	}
	/**@param param 可以是int（即msg.what），也可以是Message，最先handleMessage传进来的肯定是msg*/
	private Unit searchForSwitchCode(SootMethod mth, Local param, int depth) {
		if(depth > 10)
			return null;
		Set<Local> whatSet = new HashSet<Local>();
		Local msg = null;
		if(param.getType() instanceof PrimType)
			whatSet.add(param);
		else
			msg = param;
		
		for(Unit u : mth.getActiveBody().getUnits()){
			if(u instanceof TableSwitchStmt){
				Value key = ((TableSwitchStmt) u).getKey();
				if(whatSet.contains(key)){
					return u;
				}
			}
			else if(u instanceof DefinitionStmt){
				if(msg != null){
					Value rightOp = ((DefinitionStmt)u).getRightOp();
					if(rightOp instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) rightOp;
						Value base = ifr.getBase();
						if(base.equals(msg) && ifr.getField().getName().equals("what"))
							whatSet.add((Local) ((DefinitionStmt)u).getLeftOp());
					}
				}
			}
		}
		
		for(Unit u : iCfg.getCallsFromWithin(mth)){
			List<Value> args = ((InvokeStmt) u).getInvokeExpr().getArgs();
			int index = -1;
			if((index = args.indexOf(msg)) >= 0){
				Unit result = searchInCallee(u, index, depth);
				if(result != null)
					return result;
			}
			
			for(Local what : whatSet){
				if((index = args.indexOf(what)) >= 0){
					Unit result = searchInCallee(u, index, depth);
					if(result != null)
						return result;
				}
			}
		}
		
		return null;
	}

	private Unit searchInCallee(Unit u, int index, int depth) {
		SootMethod callee = ((InvokeStmt)u).getInvokeExpr().getMethod();
		Local prm = callee.getActiveBody().getParameterLocal(index);
//		switchContainer = callee;
//		keyParamIndex = index;
		switchContainerInvoker = (Stmt) u;
		return searchForSwitchCode(callee, prm, depth + 1);
	}

	private void addTraps() {
		if(orgMethodTraps == null || orgMethodTraps.isEmpty())
			return;
		Chain<Trap> newTrapChain = new HashChain<Trap>();
		int count = 0;
		for(Trap orgTrap = orgMethodTraps.getFirst(); orgTrap != null; orgTrap = orgMethodTraps.getSuccOf(orgTrap)){
			TrapInfo ti = newMethodTraps.get(count);
			if(ti != null && ti.isValid()){
				if(ti.handlerUnit == null)
					ti.handlerUnit = addUnitsStartFromTarget(orgTrap.getHandlerUnit(), null, null);
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
	 * @param preUnit 插入到此位置之后的位置
	 * @param switchUnit */
	private Unit addUnitsStartFromTarget(Unit startUnit, Unit preUnit, JTableSwitchStmt switchUnit) {
		if(existingUnits.containsKey(startUnit) && existingUnits.get(startUnit) != null)	
			return (Unit) existingUnits.get(startUnit);
		
		//在后续节点的添加过程中，可能会将本代码段终点的goto语句的跳转目标添加进去，因此我们要先进行一次记录
		//毕竟，我们的goto目标可能也是其他代码段的中间代码
		//如以下代码的最后一句：
		//if(msg.obj != null)
		//	msg.obj.equals("");
		//else
		//	msg.obj.equals("1");
		//msg.obj.equals("2");
		GotoStmt gotoStmt = null;
		for(Unit u = startUnit; u != null; u = targetMethodUnits.getSuccOf(u)){
			if(u instanceof GotoStmt){
				gotoStmt = (GotoStmt) u;
				existingUnits.put(gotoStmt.getTarget(), null);
				break;
			}
			if(u instanceof ReturnVoidStmt)
				break;
		}
		
		Unit result = null;
//		if(switchTableUnit != null && switchTableUnit.getTargets().contains(startUnit))
//			preUnit = switchTablePreUnit;
		for(Unit u = startUnit; u != null; u = targetMethodUnits.getSuccOf(u)){
			if(existingUnits.containsKey(u) && existingUnits.get(u) != null){	//exception处理代码并不会有return语句，而其后面的代码有可能已经被加入进去过了~
				break;	//此处不必担心是代码段的第一句，因为这种情况在本方法开头处已经处理了。
			}
			preUnit = addOneUnit(u, switchUnit, preUnit);
			if(u.equals(startUnit)){
				result = preUnit;
				existingUnits.put(startUnit, result);
			}
			if(existingUnits.containsKey(u) && existingUnits.get(u) == null)
				existingUnits.put(u, preUnit);
//			if(switchUnit && switchTableUnit != null && u.equals(switchTableUnit))	//当u就是我们的目标SwitchTable时
//				break;
			if((u instanceof GotoStmt) || (u instanceof ReturnVoidStmt) || (u.equals(switchUnit)))
				break;
		}

		return result;
	}

	private Unit addOneUnit(Unit u, JTableSwitchStmt switchUnit, Unit preUnit) {
		Unit newUnit = (Unit) u.clone();
		PatchingChain<Unit> unitsChain = myHandler.getActiveBody().getUnits(); 	
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
			Unit newTarget = addUnitsStartFromTarget(target, null, switchUnit);
			((GotoStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof IfStmt){
			Unit target = ((IfStmt) u).getTarget();
			Unit newTarget = addUnitsStartFromTarget(target, null, switchUnit);
			((IfStmt) newUnit).setTarget(newTarget);
		}
		else if(u instanceof TableSwitchStmt){
			TableSwitchStmt uu = (TableSwitchStmt) u;	//新的方案下我们的目标switchUnit在这一步被直接添加nop语句
			if(u.equals(switchUnit)){
				newUnit = new JNopStmt();
				substituteForSwitch = newUnit;
			}
			else for(int i = uu.getLowIndex(); i <= uu.getHighIndex(); i++){
				Unit target = uu.getTarget(i);
				Unit newTarget = addUnitsStartFromTarget(target, null, switchUnit);
				((TableSwitchStmt) newUnit).setTarget(i, newTarget);
			}
//			if(switchUnit && whats.contains(((TableSwitchStmt)u).getKey())){
//				switchTableUnit = (JTableSwitchStmt) u;
//				newUnit = new JNopStmt();
//				switchTablePreUnit = newUnit;
//			}
//			else for(int i = uu.getLowIndex(); i <= uu.getHighIndex(); i++){
//				Unit target = uu.getTarget(i);
//				Unit newTarget = addUnitsStartFromTarget(target, switchUnit);
//				((TableSwitchStmt) newUnit).setTarget(i, newTarget);
//			}
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
		for(Trap trap : orgMethodTraps){
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
		TrapInfo ti = newMethodTraps.get(count);
		if(ti == null){
			ti = new TrapInfo();
			ti.exception = trap.getException();
			newMethodTraps.set(count, ti);
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