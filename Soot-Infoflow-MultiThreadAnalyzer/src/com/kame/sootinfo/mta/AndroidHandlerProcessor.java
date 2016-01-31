package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.tags.MyMethodTag;
import soot.Body;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

/**
 * @throws Exception */
public class AndroidHandlerProcessor {
	private final static int FAILEDCASECODE = -1000;
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
	
	private final Logger logger = LoggerFactory.getLogger(getClass());
	
	SootClass handlerClass = Scene.v().getSootClass("android.os.Handler");
	SootClass messageClass = Scene.v().getSootClass("android.os.Message");
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
	
	List<String> handlerObtainMsgSet;
	{
		String[] obtainMsgMethods = {
				"android.os.Message obtainMessage(int)",
				"android.os.Message obtainMessage(int,java.lang.Object)",
				"android.os.Message obtainMessage(int,int,int)",
				"android.os.Message obtainMessage(int,int,int,java.lang.Object)"
		};
		handlerObtainMsgSet = Arrays.asList(obtainMsgMethods);
	}
	
	List<String> msgObtainMsgSet;
	{
		String[] obtainMsgMethods = {
				"android.os.Message obtain(android.os.Handler,int)",
				"android.os.Message obtain(android.os.Handler,int,java.lang.Object)",
				"android.os.Message obtain(android.os.Handler,int,int,int)",
				"android.os.Message obtain(android.os.Handler,int,int,int,java.lang.Object)"
		};
		msgObtainMsgSet = Arrays.asList(obtainMsgMethods);
	}
	
	private class CreateMethodReference{
		int casecode;
		SootMethod referenceMethod;
		SwitchStmt switchStmt;
		
		CreateMethodReference(int code, SootMethod refMethod, SwitchStmt switchStmt){
			this.casecode = code;
			this.referenceMethod = refMethod;
			this.switchStmt = switchStmt;
		}
	}
	
	public void run() {
		Map<Stmt, Integer> maps = findSendMSGCallerWithCaseCode();
		Map<SootMethod, CreateMethodReference> toCreateMap = new HashMap<SootMethod, CreateMethodReference>();
		for(Stmt smCaller : maps.keySet()){
			boolean isMsgToTarget = smCaller.getInvokeExpr().getMethod().equals(Scene.v().getMethod("<android.os.Message: void sendToTarget()>"));
			SootClass handlerChild = null;
			if(isMsgToTarget)	//message.sendToTarget()
				handlerChild = getTargetHandlerOfMessage(smCaller);
			else
				handlerChild = iCfg.getCalleesOfCallAt(smCaller).iterator().next().getDeclaringClass();
			int codecase = maps.get(smCaller);
			if(codecase == FAILEDCASECODE)	//TODO do some records!
				continue;
			//ok, one '_' for separation, two for '$' in handlerChild name, three for codecase when it is negative
			String suffix = "_" + handlerChild.getShortName().replace("$", "__") + "_" + codecase;
			suffix = suffix.replace("-", "___");
			
			String newDispatchSubSig = "void dispatchMessage(android.os.Message)".replace("(", suffix + "(");
			//we use newDispatch to replace the original invoke statement of hanlder.sendMessage...
			//normally, the handling codes of a message will contain a switch statement.
			//we will generate a replacement of the handnlingMethods(body of it will be generate out of this for circulation)
			//moreover, change the path between it and dispatchMessage_xxx_codecase
			SootMethod newDispatch = handlerChild.getMethodUnsafe(newDispatchSubSig);
			if(newDispatch != null){	//The newDispatch has already been added!
				replaceSendMessage(smCaller, newDispatch, suffix);
				continue;
			}

			//find the handling code of message, record the call path and find the switch statement if there is one.
			SootMethod dispathMsgOfChild = handlerChild.getMethod("void dispatchMessage(android.os.Message)");
			Map<SwitchStmt, Set<SootMethod>> pathRecords = new HashMap<SwitchStmt, Set<SootMethod>>(); 
			List<SwitchStmt> switchStmts = searchSwitchStmt(dispathMsgOfChild, dispathMsgOfChild.getActiveBody().getParameterLocal(0), new ArrayList<SootMethod>(), pathRecords);
			ensureSwitchStmtsSafe(switchStmts);
			//normally the switchStmts only has one member.
			for(SwitchStmt swStmt : switchStmts){
				SootMethod realHandler = iCfg.getMethodOf(swStmt);
				SootClass classOfHandler = realHandler.getDeclaringClass();
				
				//generate a replacement method of a simplified realHandler
//				String suffix = "_" + handlerChild.getShortName().replace("$", "__") + "_" + codecase;
				SootMethod newHandler = new SootMethod(
						realHandler.getName() + suffix, 
						realHandler.getParameterTypes(), 
						realHandler.getReturnType());
				if(classOfHandler.getMethodUnsafe(newHandler.getSubSignature()) != null)
					throw new RuntimeException(String.format("%s exist but %s not!", newHandler.getSignature(), newDispatchSubSig));
				classOfHandler.addMethod(newHandler);
				newHandler.setDeclaringClass(classOfHandler);
				
				toCreateMap.put(newHandler, new CreateMethodReference(codecase, realHandler, swStmt));
				
				Set<SootMethod> records = pathRecords.get(swStmt);
				records.add(dispathMsgOfChild);
				createAlongRecords(records, newHandler, realHandler, suffix);
			}
			newDispatch = handlerChild.getMethodUnsafe(newDispatchSubSig);
			if(newDispatch != null)
				replaceSendMessage(smCaller, newDispatch, suffix);
		}
		//let's generate the methods in toCreateMap
		//the create target if key, the reference is value.
		for(SootMethod toCreate : toCreateMap.keySet()){
			CreateMethodReference ref = toCreateMap.get(toCreate);
			Body refBody = ref.referenceMethod.getActiveBody();
			MyBodyCloneFactory cloneFactory = new MyBodyCloneFactory(null, refBody);
			cloneFactory.getNewBody().setMethod(toCreate);
			toCreate.setActiveBody(cloneFactory.getNewBody());
			//add units before switch statement.
			cloneFactory.addUnits(null, refBody.getUnits().getFirst(), ref.switchStmt);
			Unit target = null;
			if(ref.switchStmt instanceof TableSwitchStmt){
				TableSwitchStmt tss = (TableSwitchStmt)ref.switchStmt;
				if(ref.casecode >= tss.getLowIndex() && ref.casecode <= tss.getHighIndex())
					target = ref.switchStmt.getTarget(ref.casecode - tss.getLowIndex());
				else
					target = ref.switchStmt.getDefaultTarget();
			}
			else if(ref.switchStmt instanceof LookupSwitchStmt){
				int index = 0;
				LookupSwitchStmt lss = (LookupSwitchStmt) ref.switchStmt;
				while(index < lss.getTargets().size()){
					if(lss.getLookupValue(index) == ref.casecode){
						target = lss.getTarget(index);
						break;
					}
					index++;
				}
				if(target == null)
					target = lss.getDefaultTarget();
			}
			if(target == null)
				throw new RuntimeException("Can not find the target codes for " + ref.switchStmt + ". (CODE: " + ref.casecode + ")");
			cloneFactory.addUnits(cloneFactory.getSubstituteOfStop(), target, null);
			cloneFactory.completeNewTraps();
			
			CallGraphManager.optimizeCG(toCreate.getActiveBody());
			iCfg.notifyMethodChanged(toCreate);
		}
		
		Scene.v().getOrMakeFastHierarchy();
	}



	private SootClass getTargetHandlerOfMessage(Stmt sendToTargetCaller) {
		Collection<SootMethod> sms = iCfg.getCalleesOfCallAt(sendToTargetCaller);
		if(sms.size() != 1)
			throw new RuntimeException("The callees are more than one: " + sendToTargetCaller);
		SootMethod sendToTarget = sms.iterator().next();
		
		Set<Unit> callStmts = iCfg.getCallsFromWithin(sendToTarget);
		if(callStmts.size() != 1)
			throw new RuntimeException("The call statements in target method is more than one: " + sendToTarget);
		Unit unit = callStmts.iterator().next();
		Collection<SootMethod> sendMsgs = iCfg.getCalleesOfCallAt(unit);
		
		if(sendMsgs.size() != 1){
			SootClass targetClass = parseMsgTarget(sendToTargetCaller, ((InstanceInvokeExpr)sendToTargetCaller.getInvokeExpr()).getBase());
			if(targetClass != null)
				return targetClass;
			SootMethod handlerSendMsg = Scene.v().getMethod("<android.os.Handler: boolean sendMessage(android.os.Message)>");
			boolean flag = true;
			while(flag)
				flag = sendMsgs.remove(handlerSendMsg);
			if(sendMsgs.size() != 1)
				throw new RuntimeException("The callee size of " + sendToTarget + "is wrong: " + sendMsgs.size());
		}
		SootMethod sendMessage = sendMsgs.iterator().next();
		SootClass handlerChild = sendMessage.getDeclaringClass();
		return handlerChild;
	}

	private SootClass parseMsgTarget(Unit unit, Value msg) {
		for(Unit pred : iCfg.getPredsOf(unit)){
			List<ValueBox> defBoxes = pred.getDefBoxes();
			if(iCfg.isStartPoint(pred))
				return null;
			for(ValueBox box : defBoxes){
				if(box.getValue().equals(msg))
					if(((Stmt)pred).containsInvokeExpr()){
						SootClass sc = ((Stmt)pred).getInvokeExpr().getMethod().getDeclaringClass();
						if(ClassResolveManager.v().getHandlerChildren().contains(sc))
							return sc;
					}
			}
			SootClass result = parseMsgTarget(pred, msg);
			if(result != null)
				return result;
		}
		return null;
	}

	/*change the call statement of orgMethod to new method in the methods of pathRecords*/
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
				if(!orgCaller.getSubSignature().equals("void dispatchMessage(android.os.Message)"))
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
 		logger.info(String.format("Replace %s in %s with %s", smCaller.toString(), callerMethod.getSignature(), newDispatch.getSignature()));
		Body callerBody = callerMethod.getActiveBody();
		PatchingChain<Unit> callerUnits = callerBody.getUnits();
		
		String subsig = smCaller.getInvokeExpr().getMethod().getSubSignature();
		int index = sendMsgSet.indexOf(subsig);	//index = -1:msg.sendtotarget
		InstanceInvokeExpr iie = (InstanceInvokeExpr)smCaller.getInvokeExpr();
		Value base = iie.getBase();
//		Value param0 = iie.getArg(0);
		List<Value> pl = new ArrayList<Value>();
		InstanceInvokeExpr newIIE = null;
		
//		Stmt insertPos = (Stmt) callerUnits.getPredOf(smCaller);
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
			iCfg.notifyMethodChanged(callerMethod);
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
				count++;
			}
			
			Local msgObj = Jimple.v().newLocal(localName, RefType.v(messageClass));
			callerBody.getLocals().add(msgObj);
			NewExpr newExpr = Jimple.v().newNewExpr(RefType.v(messageClass));
			AssignStmt assignStmt = Jimple.v().newAssignStmt(msgObj, newExpr);
			callerUnits.insertBefore(assignStmt, smCaller);
			cg.addEdge(new Edge(callerMethod, assignStmt, Scene.v().getMethod("<android.os.Message: void <clinit>()>"), Kind.CLINIT));
			iCfg.notifyMethodChanged(callerMethod);
			SpecialInvokeExpr vInvokeExpr = Jimple.v().newSpecialInvokeExpr(msgObj, msgInit.makeRef());
			Stmt msgInitStmt = Jimple.v().newInvokeStmt(vInvokeExpr);
			callerUnits.insertBefore(msgInitStmt, smCaller);
			cg.addEdge(new Edge(callerMethod, msgInitStmt, msgInit));
			iCfg.notifyMethodChanged(callerMethod);
			pl.add(msgObj);
			newIIE = new JVirtualInvokeExpr(base, newDispatch.makeRef(), pl);
		}
		Stmt replacementStmt = null;
		if(smCaller instanceof AssignStmt){
			Value left = ((AssignStmt)smCaller).getLeftOp();
			replacementStmt = new JAssignStmt(left, newIIE);
		}else if(smCaller instanceof InvokeStmt)
			replacementStmt = new JInvokeStmt(newIIE);
		else
			throw new RuntimeException("switchContainerInvoker is neighter InvokeStmt or AssignStmt.");
		callerUnits.swapWith(smCaller, replacementStmt);
		
		CallGraphManager.optimizeCG(callerMethod.getActiveBody());
		cg.addEdge(new Edge(callerMethod, replacementStmt, newDispatch));
		cg.removeAllEdgesOutOf(smCaller);
		iCfg.notifyMethodChanged(callerMethod);
		return;
	}

	private void ensureSwitchStmtsSafe(List<SwitchStmt> switchStmts) {
		Set<SootMethod> container = new HashSet<SootMethod>();
		for(Stmt st : switchStmts){
			SootMethod sm = iCfg.getMethodOf(st);
			if(container.contains(sm))
				throw new RuntimeException("More than one target swtich statements belongs to one method.");
			container.add(sm);
		}
	}

	private Map<Stmt, Integer> findSendMSGCallerWithCaseCode() {
		Map<Stmt, Integer> result = new HashMap<Stmt, Integer>();

		List<SootClass> children = ClassResolveManager.v().getHandlerChildren();
		for(SootClass child : children){
			SootMethod dispatchInChild = child.getMethod("void dispatchMessage(android.os.Message)");
			Set<Stmt> realCallers = findRealCaller(dispatchInChild);
				for(Stmt rc : realCallers){
					List<Integer> codes = null;
					if(rc.getInvokeExpr().getMethod().equals(Scene.v().getMethod("<android.os.Message: void sendToTarget()>"))){	//message.sendToTarget() situation
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
					
					if(codes == null){
						result.put(rc, FAILEDCASECODE);
						return result;
//						throw new RuntimeException("The codes for massage object can not be parsed out." + rc);
						
					}
					List<Integer> realCodes = new ArrayList<Integer>();
					for(Integer i : codes){
						if(!realCodes.contains(i))
							realCodes.add(i);
					}
					if(realCodes.size() != 1){
						result.put(rc, FAILEDCASECODE);
						return result;
					}
//						throw new RuntimeException("The codes for massage object can not be parsed out." + rc);
					result.put(rc, realCodes.get(0));
				}
		}
		return result;
	}

	private Set<Stmt> findRealCaller(SootMethod method) {
		Set<Stmt> result = new HashSet<Stmt>();
		for(Unit caller : iCfg.getCallersOf(method)){
			SootMethod callerMethod = null;
			try{
				callerMethod = iCfg.getMethodOf(caller);
			}catch(Exception e){
				continue;
			}
			String subSignature = callerMethod.getSubSignature();
			if(sendMsgSet.contains(subSignature))
				result.addAll(findRealCaller(callerMethod));
			else if(callerMethod.equals(Scene.v().getMethod("<android.os.Message: void sendToTarget()>")))
				result.addAll(findRealCaller(callerMethod));
			else if(ClassResolveManager.v().getResolvedMethods().contains(callerMethod.getSignature()))
				result.add((Stmt) caller);
		}
		return result;
	}
	
	private boolean isMsgObtMsgInvoker(Value val) {
		if(!(val instanceof InvokeExpr))
			return false;
		SootMethod sm = ((InvokeExpr)val).getMethod();
		if(!this.msgObtainMsgSet.contains(sm.getSubSignature()))
			return false;
		return sm.getDeclaringClass().equals(Scene.v().getSootClass("android.os.Message"));
	}
	
	private boolean isHandlerObtMsgInvoker(Value val) {
		if(!(val instanceof InvokeExpr))
			return false;
		SootMethod sm = ((InvokeExpr)val).getMethod();
		if(!this.handlerObtainMsgSet.contains(sm.getSubSignature()))
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
        		if(isHandlerObtMsgInvoker(right)){//is it an Handler.obtainMessage method
	        		Value whatValue = ((VirtualInvokeExpr) right).getArgs().get(0);
	    			if(!(whatValue instanceof IntConstant))
	    				throw new RuntimeException("Message is not initialled in a normal way: " + u);
	    			else
	    				result.add(((IntConstant) whatValue).value);
        		}
        		else if(isMsgObtMsgInvoker(right)){// Message.obtain()
	        		Value whatValue = ((StaticInvokeExpr) right).getArgs().get(1);
	    			if(!(whatValue instanceof IntConstant))
	    				throw new RuntimeException("Message is not initialled in a normal way: " + u);
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
    			}else{
//    			TODO	throw new RuntimeException("Message is not initialled in a normal way: " + u);
    			}
        		return result;
        	}
        	else if(left instanceof InstanceFieldRef){//maybe msg.what = x;
        		InstanceFieldRef ifr = (InstanceFieldRef) left;
        		Value base = ifr.getBase();
        		if(base.equals(val) && ifr.getField().getName().equals("what")){	//surely msg.what = x;
        			if(right instanceof IntConstant){	//when sendEmptyMessage is invoked with constant，the assign statement is also IntConstant
        				result.add(((IntConstant) right).value);
        			}
        			else
        				throw new RuntimeException("Message is not initialled in a normal way: " + u);
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
			if(cle.getSubSignature().equals("void <clinit>()"))
				continue;
			Local prm = cle.getActiveBody().getParameterLocal(index);
			result.addAll(searchSwitchStmt(cle, prm, checkedList, pathRecords));
			for(SwitchStmt ss : result)
				pathRecords.get(ss).add(cle);
		}
		return result;
	}
}