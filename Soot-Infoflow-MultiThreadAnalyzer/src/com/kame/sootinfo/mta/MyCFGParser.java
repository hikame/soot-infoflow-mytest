package com.kame.sootinfo.mta;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.IdentityUnit;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.Ref;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.cfg.BiDirICFGFactory;
import soot.jimple.infoflow.cfg.DefaultBiDiICFGFactory;
import soot.jimple.infoflow.codeOptimization.DeadCodeEliminator;
import soot.jimple.infoflow.codeOptimization.ICodeOptimizer;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.Units;
import soot.options.Options;

public class MyCFGParser {
	protected final BiDirICFGFactory icfgFactory = new DefaultBiDiICFGFactory();
	private final Logger logger = LoggerFactory.getLogger(getClass());
	private final InfoflowConfiguration config;
	private final ISourceSinkManager ssm;
	private final ITaintPropagationWrapper taintWrapper;
	private IInfoflowCFG iCfg;
	
	public MyCFGParser(InfoflowConfiguration cf, ISourceSinkManager is, ITaintPropagationWrapper tw){
		config = cf;
		ssm = is;
		taintWrapper = tw;
	}
	
	public IInfoflowCFG getInfoflowCFG(){
		return iCfg;
	}
	
	public void start(){
		generateOriginalCFG();
		handleAndroidHandler();
		reGenerateCFG();
	}
	
	/**只对于msg是同一方法内的local变量，且在对象初始化时给出constant值作为what、或动态设置msg.what为constant时有效*/
	private void handleAndroidHandler() {
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

			for(ValueBox vb : useList){		//找到调用处的message对象并做处理
				//Search the used list to find message localvalue
				Value msgValue = vb.getValue();
				RefType msgType;
				try{
					msgType = (RefType) msgValue.getType();
				}catch(Exception e){
					continue;
				}
				SootClass msgSC = msgType.getSootClass();
				if(!msgSC.equals(Scene.v().getSootClass("android.os.Message")))
					continue;
				
				if(!(msgValue instanceof Local)){
					System.out.println("[E] The founded msg object is not a local value: " + msgValue);
					break;
				}
				
				// Target android.os.Message object is found.
				// Find the corresponding code for this message
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
				if(caseCode == null)
					break;
				
				//creat handleMSG_[n] and replace the handler.sendMessage(msg) with it in the targetMethod
				SootMethod replaceMethod = creatMSGHandler(sendMSG.getDeclaringClass(), caseCode);
				//TODO do replacement!
				
				break;	//Stop checking used boxes of the callerUnit
			}
		}
		return;
	}

	private SootMethod creatMSGHandler(SootClass declaringClass, Integer caseCode) {
		// TODO Auto-generated method stub
		return null;
	}

	private void reGenerateCFG() {
		
	}

	private void generateOriginalCFG() {
        // Perform constant propagation and remove dead code
        if (config.getCodeEliminationMode() != CodeEliminationMode.NoCodeElimination) {
			long currentMillis = System.nanoTime();
			eliminateDeadCode(ssm);
			logger.info("Dead code elimination took " + (System.nanoTime() - currentMillis) / 1E9
					+ " seconds");
        }
        if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand)
        	logger.info("Callgraph has {} edges", Scene.v().getCallGraph().size());
        iCfg = icfgFactory.buildBiDirICFG(config.getCallgraphAlgorithm(),
        		config.getEnableExceptionTracking());
	}
	
	/**
	 * Runs all code optimizers 
	 * @param sourcesSinks The SourceSinkManager
	 */
	private void eliminateDeadCode(ISourceSinkManager sourcesSinks) {
		ICodeOptimizer dce = new DeadCodeEliminator();
		dce.initialize(config);
		dce.run(iCfg, Scene.v().getEntryPoints(), sourcesSinks, taintWrapper);
	}
}
