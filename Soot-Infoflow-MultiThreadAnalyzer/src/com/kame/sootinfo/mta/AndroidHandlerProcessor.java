package com.kame.sootinfo.mta;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.kame.sootinfo.mta.tags.MyMethodTag;

import soot.Body;
import soot.IdentityUnit;
import soot.Kind;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PatchingChain;
import soot.PointsToSet;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
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
import soot.jimple.ParameterRef;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG.UnitContainer;
import soot.jimple.internal.JAssignStmt;
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
import soot.toolkits.graph.DirectedGraph;
import soot.util.Chain;
import soot.util.HashChain;

/**
 * @throws Exception */
public class AndroidHandlerProcessor {
	private static AndroidHandlerProcessor thisOnly;
	static public AndroidHandlerProcessor v(){
		if(thisOnly == null){
			thisOnly = new AndroidHandlerProcessor();
		}
		return thisOnly;
	}
	
	static public AndroidHandlerProcessor reInit(){
		thisOnly = new AndroidHandlerProcessor();
		return thisOnly;
	}
	
	SootClass handlerClass = Scene.v().getSootClass("android.os.Handler");
	SootClass messageClass = Scene.v().getSootClass("android.os.Message");
	SootMethod dispatchMsgMth = Scene.v().getMethod("<android.os.Handler: void dispatchMessage(android.os.Message)>");
	SootMethod obtMsgMth = Scene.v().getMethod("<android.os.Handler: android.os.Message obtainMessage(int)>");
	//*****************在处理过程中的中间变量************************
	IInfoflowCFG iCfg = ControlFlowGraphManager.v().getInfoflowCFG();
	Map<Unit, Unit> existingUnits = null; 	
	List<TrapInfo> newMethodTraps = null; 
	Chain<Trap> orgMethodTraps = null;
	
	SootMethod myHandler = null;
	PatchingChain<Unit> targetMethodUnits = null;
	Unit substituteForSwitch = null;
	Stmt switchMethodCaller = null;
	
	List<String> sendMsgSet;
	{
		String[] sendMsgMethods = {
			"boolean sendMessage(android.os.Message)",
			"boolean sendMessageAtFrontOfQueue(android.os.Message)",
			"boolean sendMessageAtTime(android.os.Message,long)",
			"boolean sendMessageDelayed(android.os.Message,long)",
			"boolean sendEmptyMessage(int)",
			"boolean sendEmptyMessageAtTime(int,long)",
			"boolean sendEmptyMessageDelayed(int,long)"
		};
		sendMsgSet = Arrays.asList(sendMsgMethods);
	}

	private void reInitFields() {
		existingUnits = new HashMap<Unit, Unit>(); 	
		newMethodTraps = null; 
		orgMethodTraps = null;
		myHandler = null;
		targetMethodUnits = null;
		substituteForSwitch = null;
		switchMethodCaller = null;
	}
	
CallGraph cg = Scene.v().getCallGraph();
void myTest(Map<Stmt, Integer> maps){
	for(Stmt smCaller : maps.keySet()){
//		cg.
		InstanceInvokeExpr iie = (InstanceInvokeExpr)smCaller.getInvokeExpr();
		Value base = iie.getBase();
		 PointsToSet pt = Scene.v().getPointsToAnalysis().reachingObjects((Local) base);
		System.out.println(base.toString());
	}
}

	public void handleDispatchMsg() {
		Map<Stmt, Integer> maps = findSendMSGCallerWithCaseCode();
myTest(maps);
		for(Stmt smCaller : maps.keySet()){
			reInitFields();	//对于每一个sendmessage的调用，都需要将一些域重置以支持对于新到达任务的支持
			int codecase = maps.get(smCaller);
			//TODO 学习soot-infoflow中的对象类型判定方法，或者放弃对于多个handler对象的判断。
			
			JTableSwitchStmt switchUnit = (JTableSwitchStmt) searchSwitchStmtInCallee(smCaller, 0, new ArrayList<SootMethod>());
			switchUnit.toString();
		}
		
		
		//------------------------------------------------------------------
		
		Collection<Unit> invokers = iCfg.getCallersOf(dispatchMsgMth);
		for(Unit dispatchMsgInvoker : invokers){
			reInitFields();
			SootMethod dispatchMsgContainerMethod = iCfg.getMethodOf(dispatchMsgInvoker);
			if(Options.v().debug())
				System.out.println("[KM] " + dispatchMsgContainerMethod + "--->" + dispatchMsgInvoker.toString());
			Value actualPrm = ((Stmt)dispatchMsgInvoker).getInvokeExpr().getArg(0);
			
			
//			Set<Integer> caseCodes = parseCaseCodes(dispatchMsgContainerMethod, dispatchMsgInvoker, actualPrm, 0, 0); 
			List<Integer> caseCodes = parseCaseCodes(dispatchMsgInvoker, actualPrm, new ArrayList<SootMethod>()); 
			assert caseCodes != null && !caseCodes.isEmpty();
			assert caseCodes.size() == 1;
			
			JTableSwitchStmt switchUnit = (JTableSwitchStmt) searchSwitchStmt(dispatchMsgMth, dispatchMsgMth.getActiveBody().getParameterLocal(0), new ArrayList<SootMethod>());	//handleMsgMethod的参数只有一个撒~
//			JTableSwitchStmt switchUnit = null;
			if(switchUnit == null)
				//TODO record:switchUnit == null
				continue;
			
			SootMethod myHandler = creatMSGHandler(switchUnit, caseCodes.iterator().next());
			assert myHandler != null;
			myHandler.setModifiers(Modifier.PRIVATE);
			Stmt replaceStmt = generateReplaceStmt();
			SootMethod sm = iCfg.getMethodOf(switchMethodCaller);
			sm.getActiveBody().getUnits().swapWith(switchMethodCaller, replaceStmt);
			if(invokers.size() > 1){	//TODO CHECK IT OUT
				modifyInvokers(switchMethodCaller, (Stmt) dispatchMsgInvoker);
			}else{
				CallGraph cg = Scene.v().getCallGraph();
				cg.removeAllEdgesOutOf(switchMethodCaller);
				cg.addEdge(new Edge(sm, replaceStmt, myHandler));
				iCfg.notifyMethodChanged(sm);
				iCfg.notifyMethodChanged(myHandler);
			}
		}
		ControlFlowGraphManager.v().eliminateDeadCode(MTAScene.v().getSourceSinkManager());//TODO right position???
		Scene.v().getOrMakeFastHierarchy();
	}



	private Map<Stmt, Integer> findSendMSGCallerWithCaseCode() {
		Map<Stmt, Integer> result = new HashMap<Stmt, Integer>();
		Set<Stmt> realCallers = findRealCaller(dispatchMsgMth);
		for(Stmt rc : realCallers){
			Value prm = rc.getInvokeExpr().getArg(0);
			if(prm instanceof IntConstant){
				result.put(rc, ((IntConstant) prm).value);
				continue;
			}
			List<Integer> codes = parseCaseCodes(rc, rc.getInvokeExpr().getArg(0), new ArrayList<SootMethod>());
			assert codes != null && codes.size() == 1;
			result.put(rc, codes.get(0));
		}
		return result;
	}

	private Set<Stmt> findRealCaller(SootMethod method) {
		Set<Stmt> result = new HashSet<Stmt>();
		for(Unit caller : iCfg.getCallersOf(method)){
			SootMethod callerMethod = iCfg.getMethodOf(caller);
			String subSignature = callerMethod.getSubSignature();
			if(sendMsgSet.contains(subSignature))
				result.addAll(findRealCaller(callerMethod));
			else
				result.add((Stmt) caller);
		}
		return result;
	}

	private void modifyInvokers(Stmt currentStmt, Stmt topStmt) {
		// TODO Auto-generated method stub
		return;
	}

	private Stmt generateReplaceStmt() {
		InvokeExpr invExpr = switchMethodCaller.getInvokeExpr();
		List<Value> actualArgs = invExpr.getArgs();
		
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
		if(switchMethodCaller instanceof AssignStmt){
			Value left = ((AssignStmt)switchMethodCaller).getLeftOp();
			replacementStmt = new JAssignStmt(left, newInvExpr);
		}else if(switchMethodCaller instanceof InvokeStmt){
			replacementStmt = new JInvokeStmt(newInvExpr);
		}else{
			throw new RuntimeException("switchContainerInvoker is neighter InvokeStmt or AssignStmt.");
		}
		return replacementStmt;
	}
	
	private boolean isObtMsgInvoker(Value val) {
		if(!(val instanceof InvokeExpr))
			return false;
		SootMethod sm = ((InvokeExpr)val).getMethod();
		if(sm.equals(obtMsgMth))
			return true;
		if(sm.getSignature().equals(obtMsgMth.getSignature())){
			for(SootClass sc = sm.getDeclaringClass(); sc.hasSuperclass(); sc = sc.getSuperclass())
				if(sc.equals(handlerClass))
					return true;
//			for(SootClass sc = sm.getDeclaringClass(); sc.hasOuterClass(); sc = sc.getOuterClass())
//				if(sc.equals(handlerClass))
//					return true;
		}
		return false;
	}
	
	private List<Integer> parseCaseCodes(Unit u, Value val, ArrayList<SootMethod> checkedList) {
		List<Integer> result = new ArrayList<Integer>();
		if(u instanceof DefinitionStmt){
        	Value left = ((DefinitionStmt) u).getLeftOp();
    		Value right = ((DefinitionStmt) u).getRightOp();
        	if(left.equals(val)){	//msg已经被污染，不论是否找到，都要被返回了
        		if(isObtMsgInvoker(right)){//查证是否是obtainMessage
	        		Value whatValue = ((VirtualInvokeExpr) right).getArgs().get(0);
	    			if(!(whatValue instanceof IntConstant))	//TODO record this!
	    				System.out.println("[E] Message is not get by a constant value: " + u);
	    			else
	    				result.add(((IntConstant) whatValue).value);
        		}
        		else if(right instanceof ParameterRef){	//表示传自上层方法
    				SootMethod callerMethod = iCfg.getMethodOf(u);
    				if(!callerMethod.equals(Scene.v().getEntryPoints()) && !checkedList.contains(callerMethod)){	//当分析抵达了最上层的dummyMainMethod，则直接返回现有结果了~
						checkedList.add(callerMethod);
    					for(Unit callUnit : iCfg.getCallersOf(callerMethod)){
    						int index = ((ParameterRef)right).getIndex();
    						Value actualPrm = ((Stmt)callUnit).getInvokeExpr().getArg(index);
    						result.addAll(parseCaseCodes(callUnit, actualPrm, checkedList));
    					}
    				}
    			}//TODO record this! 可能是msg = foo();
        		return result;
        	}
        	else if(left instanceof InstanceFieldRef){//可能是msg.what = x;
        		InstanceFieldRef ifr = (InstanceFieldRef) left;
        		Value base = ifr.getBase();
        		if(base.equals(val) && ifr.getField().getName().equals("what")){	//确实是msg.what = x;
        			if(right instanceof IntConstant){	//当调用sendEmptyMessage时传入的是constant，赋值语句也会相应的是IntConstant
        				result.add(((IntConstant) right).value);
        			}
//        			else	//TODO do record about unresolved msg.what.
        			return result;	//msg.what已经被污染，需要将结果返回
        		}
        	}
		}
		
		List<Unit> preUnits = iCfg.getPredsOf(u);
		if(preUnits == null || preUnits.isEmpty())	//本方法查完，并且msg不是作为参数被传入的。
			return result;
		else for(Unit pu : preUnits)	//对于同一方法内的前节点进行分析
			result.addAll(parseCaseCodes(pu, val, checkedList));
		return result;
	}

	private SootMethod creatMSGHandler(JTableSwitchStmt switchUnit, Integer caseCode){
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
	/**@param param 可以是int（即msg.what），也可以是Message*/
	private Unit searchSwitchStmt(SootMethod mth, Local param, List<SootMethod> checkedList) {
		if(checkedList.contains(mth))
			return null;
		Set<Local> whatSet = new HashSet<Local>();
		Local msg = null;
		if(param.getType() instanceof PrimType)
			whatSet.add(param);
		else
			msg = param;
		//在本方法中寻找
		for(Unit u : mth.getActiveBody().getUnits()){
			if(u instanceof TableSwitchStmt){//找到了
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
						if(base.equals(msg) && ifr.getField().getName().equals("what"))	//是关于msg.what值的获取
							whatSet.add((Local) ((DefinitionStmt)u).getLeftOp());
					}
				}
			}
		}
		//在被调用者中寻找
		Set<Unit> tmp = iCfg.getCallsFromWithin(mth);
		for(Unit u : iCfg.getCallsFromWithin(mth)){
			List<Value> args = ((Stmt)u).getInvokeExpr().getArgs();
			int index = -1;
			if((index = args.indexOf(msg)) >= 0){
				Unit result = searchSwitchStmtInCallee(u, index, checkedList);
				if(result != null)
					return result;
			}
			
			for(Local what : whatSet){
				if((index = args.indexOf(what)) >= 0){
					Unit result = searchSwitchStmtInCallee(u, index, checkedList);
					if(result != null)
						return result;
				}
			}
		}
		
		return null;
	}

	private Unit searchSwitchStmtInCallee(Unit callStmt, int index, List<SootMethod> checkedList) {
		Collection<SootMethod> callees = iCfg.getCalleesOfCallAt(callStmt);
		
		if(callees.size() == 0)
			return null;
		SootMethod realCallee = null;
		if(callees.size() == 1)
			realCallee = callees.iterator().next();
		else for(SootMethod cle : callees){	//invoke handler.handlerMessage() 可能会调用方法的当handler有多个继承class时的时候就会有多个。
//			iCfg.getStartPointsOf(cle);
//			TODO
			CallGraph cg = Scene.v().getCallGraph();
			Iterator<Edge> edges = cg.edgesInto(cle);
//			while(edges.hasNext()){
//				Edge e = edges.next();
//				System.out.println(e.toString());
//				SootMethod sm = cg.g
//			}
			Local thisInCallee = cle.getActiveBody().getThisLocal();
			List<UnitBox> tmp = ((Stmt)callStmt).getBoxesPointingToThis();//!!!向前回溯到senmessagexxx即可！
			InvokeExpr ie = ((Stmt)callStmt).getInvokeExpr();
			Value thisInCallerStmt= ((InstanceInvokeExpr) ie).getBase();
			Value thisInCaller = iCfg.getMethodOf(callStmt).getActiveBody().getThisLocal();
			boolean stmtb = thisInCallee.equals(thisInCallerStmt);
			boolean callerb = thisInCaller.equals(thisInCaller);
			thisInCallee.toString();
		}
		Local prm = realCallee.getActiveBody().getParameterLocal(index);
		switchMethodCaller = (Stmt) callStmt;
		return searchSwitchStmt(realCallee, prm, checkedList);
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
		Scene.v().getCallGraph().addEdge(newEdge);
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
}