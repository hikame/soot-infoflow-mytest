package com.kame.sootinfo.mta;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import soot.Body;
import soot.Kind;
import soot.Local;
import soot.Pack;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;

/**只对于msg是同一方法内的local变量，且在对象初始化时给出constant值作为what、或动态设置msg.what为constant时有效
 * @throws Exception */
public class MyHandlerHandler {
	private IInfoflowCFG iCfg;
	
	

	public boolean start(IInfoflowCFG iCfg) throws Exception{
		this.iCfg = iCfg;
		return handleAndroidHandler();
	}
	
	private boolean handleAndroidHandler() throws Exception {
		boolean changed = false;
		SootMethod sendMSG = null;
		sendMSG = Scene.v().getMethod("<android.os.Handler: boolean sendMessage(android.os.Message)>");
		
		Collection<Unit> unitCollection = iCfg.getCallersOf(sendMSG);
		for(Unit callerUnit : unitCollection){	//每个sendMsg的调用处
			SootMethod callerSM = iCfg.getMethodOf(callerUnit);
			if(Options.v().debug())
				System.out.println("[KM] " + callerSM + "--->" + callerUnit.toString());
			List<ValueBox> useList = callerUnit.getUseBoxes();
			if(useList == null || useList.isEmpty())
				continue;

			Value msgValue = null, hdValue = null;
			for(ValueBox vb : useList){		//找到调用处的message对象并做处理
				//Search the used list to find message localvalue
				Value tmpValue = vb.getValue();
				RefType tmpType = null;
				try{
					tmpType = (RefType) tmpValue.getType();
				}catch(Exception e){
					continue;
				}

				SootClass tmpClass = tmpType.getSootClass();
				SootClass handlerClass = Scene.v().getSootClass("android.os.Handler");
				if(tmpClass.equals(Scene.v().getSootClass("android.os.Message"))){
					if(!(tmpValue instanceof Local)){
						System.out.println("[E] The founded msg object is not a local value: " + tmpValue);
						break;
					}
					else{
						msgValue = tmpValue;
					}
				}
				else if(tmpClass.equals(handlerClass) || tmpClass.getSuperclass().equals(handlerClass))
					hdValue = tmpValue;
			}
			if(msgValue == null || hdValue == null)
				continue;
			
			Integer caseCode = parseCaseCode(callerSM, msgValue, callerUnit); 
			if(caseCode == null)
				break;
			SootMethod replaceMethod = creatMSGHandler(callerUnit, hdValue, caseCode);
			if(replaceMethod == null){
				System.out.println("[E] Can not creat the replace method for handlerMessage() normally: " + callerUnit);
				continue;
			}
			PatchingChain<Unit> smUnits = callerSM.getActiveBody().getUnits();
			Stmt replaceStmt = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr((Local)hdValue, replaceMethod.makeRef(), msgValue));
			smUnits.swapWith(callerUnit, replaceStmt);
			
			CallGraph cg = Scene.v().getCallGraph();
//			cg.swapEdgesOutOf((Stmt) callerUnit, replaceStmt);
			boolean b = cg.removeAllEdgesOutOf(callerUnit);
			cg.addEdge(new Edge(callerSM, replaceStmt, ((InvokeStmt) replaceStmt).getInvokeExpr().getMethod()));
			
			System.out.println(cg.toString());
			System.out.println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
			
			//需要以新加的方法myhandler[n]为起点，将其内部的调用关系进行后续分析。
			changed = true;
		}
		return changed;
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
		CallGraph cg = Scene.v().getCallGraph();
		
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

		PatchingChain<Unit> hdMsgUnits = handleMsg.getActiveBody().getUnits();

		SootMethod myHandler = new SootMethod(
				"myHandler" + caseCode, 
				Collections.singletonList((Type)RefType.v("android.os.Message")), 
				VoidType.v());
		SootClass sc = handleMsg.getDeclaringClass();
		try{
			sc.addMethod(myHandler);
		}catch(Exception e){
			return sc.getMethod(myHandler.getSubSignature());
		}
		
		Body myThinBody = Jimple.v().newBody();
		myThinBody.setMethod(myHandler);
		myHandler.setActiveBody(myThinBody);
//		LocalGenerator lg = new LocalGenerator(myThinBody);
		PatchingChain<Unit> myUnitsChain = myThinBody.getUnits();
		
		for(Local loc : handleMsg.getActiveBody().getLocals()){
//	        Local sootLocal = soot.jimple.Jimple.v().newLocal(loc.getName(), loc.getType());
//	        body.getLocals().add(sootLocal);
			myThinBody.getLocals().add(loc);
		}
		
		JTableSwitchStmt switchTable = null;
		for(Unit u : hdMsgUnits){
			if(u instanceof SwitchStmt){
				switchTable = (JTableSwitchStmt) u;
				break;
			}
			addUnitToTargetBody(myUnitsChain, u, cg, myHandler);
//			myUnitsChain.add(u);
		}
		if(switchTable == null)
			return null;

		Unit targetUnit = switchTable.getTarget(caseCode - switchTable.getLowIndex());
		
		while(targetUnit != null){
			if(targetUnit instanceof GotoStmt){
				GotoStmt gt = (GotoStmt) targetUnit;
				targetUnit = gt.getTarget();
				continue;
			}
			addUnitToTargetBody(myUnitsChain, targetUnit, cg, myHandler);
//			myUnitsChain.add(targetUnit);
			targetUnit = hdMsgUnits.getSuccOf(targetUnit);
		}
		
		return myHandler;
	}

	private void addUnitToTargetBody(PatchingChain<Unit> myUnitsChain, Unit u, CallGraph cg, SootMethod myHandler) {
		myUnitsChain.add(u);
		if(u instanceof InvokeStmt){
			SootMethod tgt = ((InvokeStmt) u).getInvokeExpr().getMethod();
			Kind kind = cg.findEdge(u, tgt).kind();
			Edge newEdge = new Edge(myHandler, u, tgt, kind);
			cg.addEdge(newEdge);
		}
	}

}
