package com.kame.sootinfo.mta;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
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
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
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
	Stmt switchContainerInvoker = null;



	private void reInitFields() {
		existingUnits = new HashMap<Unit, Unit>(); 	
		newMethodTraps = null; 
		orgMethodTraps = null;
		myHandler = null;
		targetMethodUnits = null;
		substituteForSwitch = null;
		switchContainerInvoker = null;
	}
	
	public void handleDispatchMsg() {
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
			
			JTableSwitchStmt switchUnit = (JTableSwitchStmt) searchForSwitchCode(dispatchMsgMth, dispatchMsgMth.getActiveBody().getParameterLocal(0), 0);	//handleMsgMethod的参数只有一个撒~
			if(switchUnit == null)
				//TODO record:switchUnit == null
				continue;
			
			SootMethod myHandler = creatMSGHandler(switchUnit, caseCodes.iterator().next());
			assert myHandler != null;
			myHandler.setModifiers(Modifier.PRIVATE);
			Stmt replaceStmt = generateReplaceStmt();
			SootMethod sm = iCfg.getMethodOf(switchContainerInvoker);
			sm.getActiveBody().getUnits().swapWith(switchContainerInvoker, replaceStmt);
			if(invokers.size() > 1){	//TODO CHECK IT OUT
				modifyInvokers(switchContainerInvoker, (Stmt) dispatchMsgInvoker);
			}else{
				CallGraph cg = Scene.v().getCallGraph();
				cg.removeAllEdgesOutOf(switchContainerInvoker);
				cg.addEdge(new Edge(sm, replaceStmt, myHandler));
				iCfg.notifyMethodChanged(sm);
				iCfg.notifyMethodChanged(myHandler);
			}

			
//			return;
//			CallGraph cg = Scene.v().getCallGraph();
//			boolean b = cg.removeAllEdgesOutOf(switchContainerInvoker);
//			cg.addEdge(new Edge(sm, replaceStmt, myHandler));
		}
		ControlFlowGraphManager.v().eliminateDeadCode(MTAScene.v().getSourceSinkManager());//TODO right position???
		Scene.v().getOrMakeFastHierarchy();
	}

	private void modifyInvokers(Stmt currentStmt, Stmt topStmt) {
		// TODO Auto-generated method stub
		
	}

	private Stmt generateReplaceStmt() {
		InvokeExpr invExpr = switchContainerInvoker.getInvokeExpr();
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


	
//	private List<Integer> parseWhatValue(Unit u, Value val) {
//		List<Integer> result = new ArrayList<Integer>();
//		if((u instanceof IdentityUnit) 
//				&& ((IdentityUnit) u).getLeftOp().equals(val)){	//找到了，但有可能是传进来的参数
//			Value right = ((IdentityUnit) u).getRightOp();
//			if(right instanceof IntConstant)	//表示顺利找到
//				result.add(((IntConstant) right).value);
//			else if(right instanceof ParameterRef){	//表示传自上层方法
//				SootMethod callerMethod = iCfg.getMethodOf(u);
//				if(!callerMethod.equals(Scene.v().getEntryPoints())){	//当分析抵达了最上层的dummyMainMethod，则直接返回现有结果了~
//					for(Unit callUnit : iCfg.getCallersOf(callerMethod)){
//						int index = ((ParameterRef)right).getIndex();
//						Value actualPrm = ((Stmt)callUnit).getInvokeExpr().getArg(index);
//						result.addAll(parseWhatValue(callUnit, actualPrm));
//					}
//				}
//			}//上述两种情况之外的表示是一个动态变量，无法解析，需要记录 TODO
//			return result;
//		}
//		
//		List<Unit> preUnits = iCfg.getPredsOf(u);
//		if(preUnits == null || preUnits.isEmpty())		//该方法内的节点分析完毕，并且没有来自上级参数的what值的传递
//			return result;
//		else for(Unit pu : preUnits)	//对于同一方法内的前节点进行分析
//			result.addAll(parseWhatValue(pu, val));
//		return result;
//	}

//
//	private Set<Integer> parseCaseCodes(SootMethod thisSootMethod,  Unit invokeUnit, Value msgValue, int index, int depth) {
//		Body callerBody = thisSootMethod.getActiveBody();
//        PatchingChain<Unit> unitsChain = callerBody.getUnits();
//        Set<Integer> caseCodes = new HashSet<Integer>();
//        for(Unit u = invokeUnit; u != null; u = unitsChain.getPredOf(u)){	//TODO 思路不是很对应该用icfg
//        	if(!(u instanceof AssignStmt)){
//        		continue;
//        	}
//        	Value left = ((AssignStmt) u).getLeftOp();
//    		Value right = ((AssignStmt) u).getRightOp();
//        	if(left.equals(msgValue) && 
//        			(right instanceof VirtualInvokeExpr) &&
//        			((VirtualInvokeExpr) right).getMethod().equals(
//	        				Scene.v().getMethod(
//	        						"<android.os.Handler: "
//	        						+ "android.os.Message obtainMessage(int)>"))){
//        		Value whatValue = ((VirtualInvokeExpr) right).getArgs().get(0);
//    			if(!(whatValue instanceof IntConstant)){
//    				System.out.println("[E] Message is not get by a constant value: " + u);
//    				break;
//    			}
//    			caseCodes.add(((IntConstant) whatValue).value);
//    			break;
//        	}
//        	if(left instanceof InstanceFieldRef){
//        		InstanceFieldRef ifr = (InstanceFieldRef) left;
//        		Value base = ifr.getBase();
//        		if(base.equals(msgValue) && ifr.getField().getName().equals("what")){
//        			if(right instanceof IntConstant){	//当调用sendEmptyMessage时传入的是constant，赋值语句也会相应的是IntConstant
//        				caseCodes.add(((IntConstant) right).value);
//        				break;
//        			}
//        			else	//TODO do record about unresolved msg.what.
//        				break;
//        		}
//        	}
//        }
//        if(!MTAScene.v().getTargetList().contains(thisSootMethod.getSignature())){	//search for case code in its caller
//        	for(Unit u : iCfg.getCallersOf(thisSootMethod)){
//        		List<Value> actualParams = ((Stmt)u).getInvokeExpr().getArgs();
//        		SootMethod sm = iCfg.getMethodOf(u);
//        		int count = 0;
//        		Value ap = null;
//        		for(Value value : actualParams){
//        			Type type = value.getType();
//        			if(type instanceof RefType && ((RefType)type).getSootClass().equals(messageClass)){
//        				ap = value;
//        				break;
//        			}
//        			count++;
//        		}
//        		if(ap != null && depth < MAX_CASECODE_SEARCH_DEPTH)
//        			caseCodes.addAll(parseCaseCodes(sm, u, ap, count, depth + 1));
//        	}
//        }
//		return caseCodes;
//	}
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
		//在本方法中寻找
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
		//在被调用者中寻找
		for(Unit u : iCfg.getCallsFromWithin(mth)){
			List<Value> args = ((Stmt)u).getInvokeExpr().getArgs();
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
		Collection<SootMethod> cles = iCfg.getCalleesOfCallAt(u);
		assert cles.size() <= 1;
		if(cles.size() == 0)
			return null;
		SootMethod callee = iCfg.getCalleesOfCallAt(u).iterator().next();
		Local prm = callee.getActiveBody().getParameterLocal(index);
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