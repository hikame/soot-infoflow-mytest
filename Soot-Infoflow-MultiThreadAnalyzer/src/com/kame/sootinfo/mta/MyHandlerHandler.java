package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.Kind;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;

/**
 * @throws Exception */
public class MyHandlerHandler {
	private IInfoflowCFG iCfg;
	
	private Map<Unit, Unit> existingTargets; 	
	JTableSwitchStmt switchTableUnit = null;
	Unit switchTablePreUnit = null;
	List<Value> whats = new ArrayList<Value>();
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

		myHandler = new SootMethod(
				"myHandler" + caseCode, 
				Collections.singletonList((Type)RefType.v("android.os.Message")), 
				VoidType.v());
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
		return myHandler;
	}
	
	/**it will append the codes starting from startUnit and end with null or goto stmt
	 * the the return value is the new unit in the created method.
	 * @param searchForSwitchTable */
	private Unit addUnitsStartFromTarget(Unit startUnit, boolean searchForSwitchTable) {
		if(existingTargets.containsKey(startUnit))	
			return (Unit) existingTargets.get(startUnit);
		
		Unit result = null;
		Unit preUnit = null;
//		if(startUnit.equals(switchTableUnit))
		if(switchTableUnit != null && switchTableUnit.getTargets().contains(startUnit))
			preUnit = switchTablePreUnit;
		for(Unit u = startUnit; u != null; u = hdMsgUnits.getSuccOf(u)){
			preUnit = addOneUnit(u, searchForSwitchTable, preUnit);
			if(u.equals(startUnit)){
				result = preUnit;
				existingTargets.put(startUnit, result);
			}
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
			SootMethod tgt = invokeExpr.getMethod();
			Kind kind = Edge.ieToKind(invokeExpr);
			Edge newEdge = new Edge(myHandler, newUnit, tgt, kind);
			cg.addEdge(newEdge);
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
		else if((u instanceof AssignStmt) && ((AssignStmt) u).getRightOp().toString().equals(jifr.toString()))
			whats.add(((AssignStmt)u).getLeftOp());
		if(preUnit == null)
			unitsChain.add(newUnit);
		else
			unitsChain.insertAfter(newUnit, preUnit);
		//TODO：实践证明这样做还是很有问题的！需要用精确地insertAfter  
//		???关于newUnit的插入位置目前存疑，是否需要记录其prenode呢？或是用下面这条语句呢？
		return newUnit;
	}

}