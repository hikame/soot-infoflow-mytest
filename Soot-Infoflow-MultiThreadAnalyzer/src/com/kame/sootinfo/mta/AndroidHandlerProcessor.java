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
import com.kame.sootinfo.mta.tags.MyStmtTag;

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
import soot.jimple.LookupSwitchStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;
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
	String dispatchSubSignature = "void dispatchMessage(android.os.Message)";
	IInfoflowCFG iCfg = ControlFlowGraphManager.v().getInfoflowCFG();
	CallGraph cg = Scene.v().getCallGraph();
	
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
	
	List<String> obtainMsgSet;
	{
		String[] obtainMsgMethods = {
				"android.os.Message obtainMessage(int)",
				"android.os.Message obtainMessage(int,java.lang.Object)",
				"android.os.Message obtainMessage(int,int,int)",
				"android.os.Message obtainMessage(int,int,int,java.lang.Object)",
		};
		obtainMsgSet = Arrays.asList(obtainMsgMethods);
	}
	
	SootMethod sendToTarget = Scene.v().getMethod("<android.os.Message: void sendToTarget()>");

	public void handleDispatchMsg() {
		Map<Stmt, Integer> maps = findSendMSGCallerWithCaseCode();
		for(Stmt smCaller : maps.keySet()){
			boolean isMsgToTarget = smCaller.getInvokeExpr().getMethod().equals(this.sendToTarget);
			SootClass handlerChild = null;
			if(isMsgToTarget)	//message.sendToTarget()
				handlerChild = getHandlerChildFromMessage(smCaller);
			else
				handlerChild = iCfg.getCalleesOfCallAt(smCaller).iterator().next().getDeclaringClass();
			int codecase = maps.get(smCaller);
			String suffix = "_" + handlerChild.getShortName().replace("$", "__") + "_" + codecase;
			String newDispatchSubSig = dispatchSubSignature.replace("(", suffix + "(");
			SootMethod newDispatch = handlerChild.getMethodUnsafe(newDispatchSubSig);
			if(newDispatch != null){	//The newDispatch has already been added!
				replaceSendMessage(smCaller, newDispatch, suffix);
				continue;
			}
			//create new methods and replace them starting from dispatch() method.
			SootMethod dispathMsgOfChild = handlerChild.getMethod(dispatchSubSignature);
			Map<SwitchStmt, Set<SootMethod>> pathRecords = new HashMap<SwitchStmt, Set<SootMethod>>(); 
			List<SwitchStmt> switchStmts = searchSwitchStmt(dispathMsgOfChild, dispathMsgOfChild.getActiveBody().getParameterLocal(0), new ArrayList<SootMethod>(), pathRecords);
			ensureSwitchStmtsSafe(switchStmts);//TODO do some record;
			for(SwitchStmt swStmt : switchStmts){
				SootMethod orgMethod = iCfg.getMethodOf(swStmt); 
				Body orgbody = orgMethod.getActiveBody();
				SootClass sc = orgMethod.getDeclaringClass();
				SootMethod newMethod = new SootMethod(
						orgMethod.getName() + "_" + dispathMsgOfChild.getDeclaringClass().getShortName().replace("$", "__") + "_" + codecase, 
						orgMethod.getParameterTypes(), 
						orgMethod.getReturnType());

				assert (sc.getMethodUnsafe(newMethod.getSubSignature()) == null);
				sc.addMethod(newMethod);
				newMethod.setDeclaringClass(sc);
				
				MyBodyCloneFactory bcf = new MyBodyCloneFactory(null, orgbody);
				bcf.getNewBody().setMethod(newMethod);
				newMethod.setActiveBody(bcf.getNewBody());
				bcf.addUnits(null, orgbody.getUnits().getFirst(), swStmt);
				Unit target = null;
				if(swStmt instanceof TableSwitchStmt){
					TableSwitchStmt tss = (TableSwitchStmt)swStmt;
					if(codecase >= tss.getLowIndex() && codecase <= tss.getHighIndex())
						target = swStmt.getTarget(codecase - tss.getLowIndex());
					else
						target = swStmt.getDefaultTarget();
				}
				else if(swStmt instanceof LookupSwitchStmt){
					int index = 0;
					LookupSwitchStmt lss = (LookupSwitchStmt) swStmt;
					while(index < lss.getTargets().size()){
						if(lss.getLookupValue(index) == codecase){
							target = lss.getTarget(index);
							break;
						}
						index++;
					}
					if(target == null)
						target = lss.getDefaultTarget();
				}
				assert target != null;
				bcf.addUnits(bcf.getSubstituteOfStop(), target, null);
				bcf.completeNewTraps();

				CallGraphManager.optimizeCG(newMethod.getActiveBody());
				iCfg.notifyMethodChanged(newMethod);

				//by now, have successifully created the new body!
				//replace the orgMethod invoke path with new one.
				Set<SootMethod> records = pathRecords.get(swStmt);
				records.add(dispathMsgOfChild);
				createAlongRecords(records, newMethod, orgMethod, suffix);
			}
			newDispatch = handlerChild.getMethod(newDispatchSubSig);
			replaceSendMessage(smCaller, newDispatch, suffix);
		}
		Scene.v().getOrMakeFastHierarchy();
	}



	private SootClass getHandlerChildFromMessage(Stmt smCaller) {
		Collection<SootMethod> sms = iCfg.getCalleesOfCallAt(smCaller);
		assert sms.size() == 1;
		SootMethod sendToTarget = sms.iterator().next();
		Set<Unit> callStmts = iCfg.getCallsFromWithin(sendToTarget);
		assert callStmts.size() == 1;
		Unit unit = callStmts.iterator().next();
		Collection<SootMethod> sendMsgs = iCfg.getCalleesOfCallAt(unit);
		assert sendMsgs.size() == 1;
		SootMethod sendMessage = sendMsgs.iterator().next();
		SootClass handlerChild = sendMessage.getDeclaringClass();
		return handlerChild;
	}

	private void createAlongRecords(Set<SootMethod> pathRecords, SootMethod newMethod, SootMethod orgMethod, String suffix) {
		Collection<Unit> callUnits = iCfg.getCallersOf(orgMethod);
		for(Unit callUnit : callUnits){
			SootMethod orgCaller = iCfg.getMethodOf(callUnit);			
			if(!pathRecords.contains(orgCaller))
				continue;
			
			List<Unit> orgUnits = new ArrayList<Unit>(orgCaller.getActiveBody().getUnits());
			List<Unit> newUnits = null;
			int index = orgUnits.indexOf(callUnit);
			
			String newCallerSig = orgCaller.getSubSignature().replace("(", suffix + "(");
			SootClass callerClass = orgMethod.getDeclaringClass();
			SootMethod newCaller = callerClass.getMethodUnsafe(newCallerSig);
			if(newCaller != null){
				SootMethod orgCallee = ((Stmt)newCaller.getActiveBody().getAllUnitBoxes().get(index)).getInvokeExpr().getMethod();
				if(orgCallee.equals(newMethod))	//this peace of code has already been handled!
					continue;
				newUnits = new ArrayList<Unit>(newCaller.getActiveBody().getUnits());
			}
			else{	//we need to create one and add it to the caller class.
				newCaller = new SootMethod(orgCaller.getName() + suffix, orgCaller.getParameterTypes(),	orgCaller.getReturnType());
				//handling MyMethodTag
				MyMethodTag mmt = (MyMethodTag) orgCaller.getTag(MyMethodTag.class.getName());
				if(mmt != null && mmt.isMultithread())
					newCaller.addTag(mmt);
				
				newCaller.setDeclaringClass(callerClass);
				callerClass.addMethod(newCaller);
				Body newCallerBody = (Body) orgCaller.getActiveBody().clone();
				newCaller.setActiveBody(newCallerBody);
				if(!orgCaller.getSubSignature().equals(dispatchSubSignature))
					createAlongRecords(pathRecords, newCaller, orgCaller, suffix);
				
				for(int i = 0; i < orgUnits.size(); i++){	//configure the call graph
					Stmt os = (Stmt) orgUnits.get(i);
					if(!os.containsInvokeExpr())
						continue;
					SootMethod callee = null;
					Collection<SootMethod> callees = iCfg.getCalleesOfCallAt(os);
					if(callees.size() == 1)
						callee = callees.iterator().next();
					else if(callees.size() > 1)
						callee = os.getInvokeExpr().getMethod();
					newUnits = new ArrayList<Unit>(newCaller.getActiveBody().getUnits());
					if(callee != null && !callee.equals(orgMethod))
						cg.addEdge(new Edge(newCaller, (Stmt)newUnits.get(i), callee));
				}
			}
			
			Stmt invokeStmt = ((Stmt) newUnits.get(index));
			InvokeExpr ie = invokeStmt.getInvokeExpr();
			ie.setMethodRef(newMethod.makeRef());
			
			MyMethodTag mmt = (MyMethodTag) orgCaller.getTag(MyMethodTag.class.getSimpleName());
			if(mmt != null && mmt.isMultithread())
				newCaller.addTag(mmt);
			cg.addEdge(new Edge(newCaller, invokeStmt, newMethod));
			iCfg.notifyMethodChanged(newCaller);
//			CallGraphManager.optimizeCG(newCaller.getActiveBody());
		}
	}

	private void replaceSendMessage(Stmt smCaller, SootMethod newDispatch, String suffix) {
 		SootMethod callerMethod = iCfg.getMethodOf(smCaller);
		Body callerBody = callerMethod.getActiveBody();
		PatchingChain<Unit> callerUnits = callerBody.getUnits();
		
		String subsig = smCaller.getInvokeExpr().getMethod().getSubSignature();
		int index = sendMsgSet.indexOf(subsig);	//index = -1:msg.sendtotarget
		InstanceInvokeExpr iie = (InstanceInvokeExpr)smCaller.getInvokeExpr();
		Value base = iie.getBase();
//		Value param0 = iie.getArg(0);
		List<Value> pl = new ArrayList<Value>();
		InstanceInvokeExpr newIIE = null;
		if(index < 0){	//msg.sendtotarget
			SootClass msgCls = ((RefType) base.getType()).getSootClass();
			SootMethod getTargetMethod = msgCls.getMethod("android.os.Handler getTarget()");
			InvokeExpr getTargetExper = Jimple.v().newVirtualInvokeExpr((Local) base, getTargetMethod.makeRef());
			Local hdObj = null;
			for(int i = 0; hdObj == null; i++){	//make sure the local value does not exists
				String name = "handler" + i;
				for(Local loc : callerBody.getLocals()){
					if(!loc.getName().equals(name)){
						hdObj = Jimple.v().newLocal(name, RefType.v(msgCls));
						callerBody.getLocals().add(hdObj);
						break;
					}
				}
			}
			AssignStmt assignStmt = Jimple.v().newAssignStmt(hdObj, getTargetExper);
			callerUnits.insertBefore(assignStmt, smCaller);
			cg.addEdge(new Edge(callerMethod, assignStmt, getTargetMethod));
			pl.add(base);
			newIIE = new JVirtualInvokeExpr(hdObj, newDispatch.makeRef(), pl);
		}
		else if(index <= 3){	//send message
			pl.add(iie.getArg(0));
			newIIE = new JVirtualInvokeExpr(base, newDispatch.makeRef(), pl);
		}
		else{	//send emptymessage.
			SootMethod msgInit = messageClass.getMethod("void <init>()");
			int count = 0;
			String localName = "msg_KAME";
			while(count < 100){
				boolean exist = false;
				for(Local loc : callerBody.getLocals()){
					if(loc.getName().equals(localName + count)){
						exist = true;
						break;
					}
				}
				if(!exist){
					localName = localName + count;
					break;
				}
			}
			
			Local msgObj = Jimple.v().newLocal(localName, RefType.v(messageClass));
			callerBody.getLocals().add(msgObj);
			NewExpr newExpr = Jimple.v().newNewExpr(RefType.v(messageClass));
			AssignStmt assignStmt = Jimple.v().newAssignStmt(msgObj, newExpr);
			callerUnits.insertBefore(assignStmt, smCaller);
			SpecialInvokeExpr vInvokeExpr = Jimple.v().newSpecialInvokeExpr(msgObj, msgInit.makeRef());
			Stmt msgInitStmt = Jimple.v().newInvokeStmt(vInvokeExpr);
			callerUnits.insertBefore(msgInitStmt, smCaller);
			cg.addEdge(new Edge(callerMethod, msgInitStmt, msgInit));
			pl.add(msgObj);
			newIIE = new JVirtualInvokeExpr(base, newDispatch.makeRef(), pl);
		}
		Stmt replacementStmt = null;
		if(smCaller instanceof AssignStmt){
			Value left = ((AssignStmt)smCaller).getLeftOp();
			replacementStmt = new JAssignStmt(left, newIIE);
		}else if(smCaller instanceof InvokeStmt)
			replacementStmt = new JInvokeStmt(newIIE);
		else//TODO record this
			throw new RuntimeException("switchContainerInvoker is neighter InvokeStmt or AssignStmt.");
		callerUnits.swapWith(smCaller, replacementStmt);
		
//		cg.addEdge(new Edge(callerMethod, replacementStmt, newDispatch));
		cg.removeAllEdgesOutOf(smCaller);
		cg.swapEdgesOutOf(smCaller, replacementStmt);
		iCfg.notifyMethodChanged(callerMethod);
		CallGraphManager.optimizeCG(callerMethod.getActiveBody());
		
//		Iterator<Edge> tmp = cg.edgesOutOf(callerMethod);
//		List<Edge> tmpList = new ArrayList<Edge>();
//		while(tmp.hasNext())
//			tmpList.add(tmp.next());
//		Set<Unit> tmp0 = iCfg.getCallsFromWithin(callerMethod);
//		SootMethod tmp = iCfg.getMethodOf(smCaller);
		return;
	}

	private void ensureSwitchStmtsSafe(List<SwitchStmt> switchStmts) {
		Set<SootMethod> container = new HashSet<SootMethod>();
		for(Stmt st : switchStmts){
			SootMethod sm = iCfg.getMethodOf(st);
			assert !container.contains(sm);
			container.add(sm);
		}
	}

	private Map<Stmt, Integer> findSendMSGCallerWithCaseCode() {
		Map<Stmt, Integer> result = new HashMap<Stmt, Integer>();

		List<SootClass> children = ClassResolveManager.v().getHandlerChildren();
		for(SootClass child : children){
			SootMethod dispatchInChild = child.getMethod(dispatchSubSignature);
			Set<Stmt> realCallers = findRealCaller(dispatchInChild);
				for(Stmt rc : realCallers){
					List<Integer> codes = null;
					if(rc.getInvokeExpr().getMethod().equals(this.sendToTarget)){	//message.sendToTarget() situation
						Value msgValue = ((InstanceInvokeExpr)rc.getInvokeExpr()).getBase();
						codes = parseCaseCodes(rc, msgValue, new ArrayList<SootMethod>());
					}
					else{ //sendMessage situation
						Value prm = rc.getInvokeExpr().getArg(0);
						if(prm instanceof IntConstant){	//sendEmptyMessageXXX
							result.put(rc, ((IntConstant) prm).value);
							continue;
						}
						codes = parseCaseCodes(rc, rc.getInvokeExpr().getArg(0), new ArrayList<SootMethod>());
					}

					assert codes != null && codes.size() == 1;	//RECORDS!
					result.put(rc, codes.get(0));
				}
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
			else if(callerMethod.equals(this.sendToTarget))
				result.addAll(findRealCaller(callerMethod));
			else if(ClassResolveManager.v().getResolvedMethods().contains(callerMethod.getSignature()))
				result.add((Stmt) caller);
		}
		return result;
	}
	
	private boolean isObtMsgInvoker(Value val) {
		if(!(val instanceof InvokeExpr))
			return false;
		SootMethod sm = ((InvokeExpr)val).getMethod();
		if(!this.obtainMsgSet.contains(sm.getSubSignature()))
			return false;
		
		boolean isHandlerChild = Scene.v().getActiveHierarchy().isClassSubclassOf(sm.getDeclaringClass(), handlerClass);
		return isHandlerChild; 
	}
	/**@param u, the unit where we start for the backward searching.
	 * @param val, the message value we are parsing*/
	private List<Integer> parseCaseCodes(Unit u, Value val, ArrayList<SootMethod> checkedList) {
		List<Integer> result = new ArrayList<Integer>();
		if(u instanceof DefinitionStmt){
        	Value left = ((DefinitionStmt) u).getLeftOp();
    		Value right = ((DefinitionStmt) u).getRightOp();
        	if(left.equals(val)){	//msg has been tainted. return anyway.
        		if(isObtMsgInvoker(right)){//is it an obtainMessage method
	        		Value whatValue = ((VirtualInvokeExpr) right).getArgs().get(0);
	    			if(!(whatValue instanceof IntConstant))	//TODO record this!
	    				System.out.println("[E] Message is not get by a constant value: " + u);
	    			else
	    				result.add(((IntConstant) whatValue).value);
        		}
        		else if(right instanceof ParameterRef){	//表示传自上层方法
    				SootMethod callerMethod = iCfg.getMethodOf(u);
    				if(!callerMethod.equals(Scene.v().getEntryPoints()) && !checkedList.contains(callerMethod)){	//have arrived to dummyMainMethod
						checkedList.add(callerMethod);
    					for(Unit callUnit : iCfg.getCallersOf(callerMethod)){
    						int index = ((ParameterRef)right).getIndex();
    						Value actualPrm = ((Stmt)callUnit).getInvokeExpr().getArg(index);
    						result.addAll(parseCaseCodes(callUnit, actualPrm, checkedList));
    					}
    				}
    			}//TODO record this! msg = foo();
        		return result;
        	}
        	else if(left instanceof InstanceFieldRef){//maybe msg.what = x;
        		InstanceFieldRef ifr = (InstanceFieldRef) left;
        		Value base = ifr.getBase();
        		if(base.equals(val) && ifr.getField().getName().equals("what")){	//surely msg.what = x;
        			if(right instanceof IntConstant){	//when sendEmptyMessage is invoked with constant，the assign statement is also IntConstant
        				result.add(((IntConstant) right).value);
        			}
//        			else	//TODO do record about unresolved msg.what.
        			return result;	//msg.what has already been tainted.
        		}
        	}
		}
		
		List<Unit> preUnits = iCfg.getPredsOf(u);
		if(preUnits == null || preUnits.isEmpty())	//this method has been checked out. and msg is not a paramenter.
			return result;
		else for(Unit pu : preUnits)	//analyze the preunits in the same method.
			result.addAll(parseCaseCodes(pu, val, checkedList));
		return result;
	}

	/**@param param may be msg or msg.what
	 * @param pathRecords */
	private List<SwitchStmt> searchSwitchStmt(SootMethod mth, Local param, List<SootMethod> checkedList, Map<SwitchStmt, Set<SootMethod>> pathRecords) {
		List<SwitchStmt> result = new ArrayList<SwitchStmt>();
		if(checkedList.contains(mth))
			return result;
		Set<Local> whatSet = new HashSet<Local>();
		Local msg = null;
		if(param.getType() instanceof PrimType)
			whatSet.add(param);
		else
			msg = param;
		//search this method
		for(Unit u : mth.getActiveBody().getUnits()){
			if(u instanceof SwitchStmt){//findit!
				Value key = ((SwitchStmt) u).getKey();
				if(whatSet.contains(key)){
					SwitchStmt ss = (SwitchStmt) u;
					result.add(ss);
					Set<SootMethod> set = new HashSet<SootMethod>();
					set.add(mth);
					pathRecords.put(ss, set);
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
		//search in callee
		for(Unit u : iCfg.getCallsFromWithin(mth)){
			List<Value> args = ((Stmt)u).getInvokeExpr().getArgs();
			int index = -1;
			if((index = args.indexOf(msg)) >= 0){
				result.addAll(handleCallStmtForSwitchSearch(u, index, checkedList, pathRecords));
			}
			
			for(Local what : whatSet){
				if((index = args.indexOf(what)) >= 0){
					result.addAll(handleCallStmtForSwitchSearch(u, index, checkedList, pathRecords));
				}
			}
		}
		
		return result;
	}

	private List<SwitchStmt> handleCallStmtForSwitchSearch(Unit callStmt, int index, List<SootMethod> checkedList, Map<SwitchStmt, Set<SootMethod>> pathRecords) {
		List<SwitchStmt> result = new ArrayList<SwitchStmt>();
		
		Collection<SootMethod> callees = iCfg.getCalleesOfCallAt(callStmt);
		if(callees.size() == 0)
			return result;
		for(SootMethod cle : callees){	//invoke parent.foo() may result in more than one callees targeted at child.foo().
			Local prm = cle.getActiveBody().getParameterLocal(index);
			result.addAll(searchSwitchStmt(cle, prm, checkedList, pathRecords));
			for(SwitchStmt ss : result)
				pathRecords.get(ss).add(cle);
		}
		return result;
	}
}