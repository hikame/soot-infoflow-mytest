package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.tags.MyMethodTag;

import soot.Body;
import soot.Hierarchy;
import soot.IdentityUnit;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootResolver;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;
import soot.tagkit.InnerClassTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;
import soot.util.queue.QueueReader;

public class ClassResolveManager {
	private ClassResolveManager(){}
	static ClassResolveManager thisOnly = null;
	static public ClassResolveManager v(){
		if(thisOnly == null){
			thisOnly = new ClassResolveManager();
		}
		return thisOnly;
	}
	
	static public ClassResolveManager reInit(){
		thisOnly = new ClassResolveManager();
		return thisOnly;
	}
	
	private static int MAX_CLASS_RESOLVE_DEPTH = 5;
	private static int MAX_METHOD_RESOLVE_DEPTH = 5;
	
	private final Logger logger = LoggerFactory.getLogger(getClass());
	
	List<String> includeList = new ArrayList<String>();
	List<String> excludeList = new ArrayList<String>();
	List<String> nonPhantomList = new ArrayList<String>();
	List<String> invokedMths = new ArrayList<String>();
	public List<String> getResolvedMethods(){
		return invokedMths;
	}
	
	List<String> myBasicClassList = null;
	{
		String[] myBasicClassSet = {
				"java.lang.Runnable",
				"java.lang.Thread",
				"java.lang.Throwable",
				"java.lang.Exception",
				"android.os.Message",
				"android.os.Handler"
		};	
		myBasicClassList = Arrays.asList(myBasicClassSet);
	}
	
	
	String[] sendMessageMethods = {
		"boolean sendMessage(android.os.Message)",
		"boolean sendMessageAtFrontOfQueue(android.os.Message)",
		"boolean sendMessageAtTime(android.os.Message,long)",
		"boolean sendMessageDelayed(android.os.Message,long)"	
	};
	
	String dipatchMsgSubsignature = "void dispatchMessage(android.os.Message)";
	
	private List<SootClass> handlerChildren = new ArrayList<SootClass>();
	private CallGraph cg;
	private IInfoflowCFG iCfg;
	public List<SootClass> getHandlerChildren(){
		return handlerChildren;
	}
	public SootMethod targetMethod;

	/**It should be able to dynamically extend the include&nonPhantom lists.
	 * And at the same time, generate&extend the control flow graph*/
	public void start(){
		Options.v().set_include(includeList);
		Options.v().set_exclude(excludeList);
		Options.v().set_nonPhantom(nonPhantomList);
		for(String s: myBasicClassList){
			resolveClass(s, 0);
			Scene.v().forceResolve(s, SootClass.BODIES);
		}
		Scene.v().loadBasicClasses();
		patchMultiThreadClasses();	//taking care of thread.start handler.post handler.send message.sendtotarget and so on.
		for(String s : MTAScene.v().getTargetList()){	//Resolve be base class of target method.
			String clsName = s.substring(1, s.indexOf(":"));
//			nonPhantomList.add(clsName);
			Scene.v().addBasicClass(clsName, SootClass.BODIES);
			SootClass base = resolveClass(clsName, 0);	//TODO does it need: resolve to body?
			Scene.v().forceResolve(base.getName(), SootClass.BODIES);
			List<Tag> tags = base.getTags();
			for(Tag tag : tags){
				if(!(tag instanceof InnerClassTag))
					continue;
				String inner = ((InnerClassTag) tag).getInnerClass().replace("/", ".");
				resolveClass(inner, 0);	//It should not be BODIES because that Some of the methods in tagged class may be subclass of android.os.Handler
			}
		}

		for(SootClass sc : Scene.v().getClasses(SootClass.SIGNATURES)){
			if(!sc.isPhantom())
				Scene.v().forceResolve(sc.getName(), SootClass.BODIES);
		}
		
		setDummyEntryPoints();	//generate the dummy main method.
		targetMethod = Scene.v().getMethod(MTAScene.v().getTargetList().get(0));
		
		CallGraphManager.v().constructCallgraph();//it will be used for long
		ControlFlowGraphManager.v().generateCFG();	//it is used for temp
		cg = Scene.v().getCallGraph();
		iCfg = ControlFlowGraphManager.v().getInfoflowCFG();
		
Iterator<Edge> edges = cg.edgesOutOf(targetMethod);
List<Edge> edgesList = new ArrayList<Edge>();
while(edges.hasNext()){
	edgesList.add(edges.next());
}
Set<Unit> callees = iCfg.getCallsFromWithin(targetMethod);
List<Unit> calleeList = new ArrayList<Unit>(callees);
List<List<SootMethod>> calleeMethodList = new ArrayList<List<SootMethod>>();
for(Unit cle : callees){
	calleeMethodList.add(new ArrayList<SootMethod>(iCfg.getCalleesOfCallAt(cle)));
}

logger.info("[T] Finished generating the call graph.");
SootClass subSC = Scene.v().getSootClass("com.kame.tafhd.MainActivity$AnotherHandler");
ReachableMethods rm = Scene.v().getReachableMethods();
QueueReader<MethodOrMethodContext> ls = rm.listener();
while(ls.hasNext()){
	System.out.println("[T] " + ls.next().toString());
}
		// In fact, this part of codes should not be useful. because any codes in the subclass of Handler should not be resolved at BODIES level. 
		// Modify the children of handler which are initialed from the start method resolving.

		List<SootMethod> startPoints = Scene.v().getEntryPoints();
		assert startPoints.size() == 1;
		String startMethd = startPoints.get(0).getSignature();
		List<String> list = new ArrayList<String>();
		list.add(startMethd);
logger.info("[T] Start doning the resolving.");
		doResolve(list);
		
		Scene.v().getSootClass("android.os.Handler").getMethod(this.dipatchMsgSubsignature).addTag(new MyMethodTag(true));
		for(SootClass sc : handlerChildren){
			SootMethod sm = sc.getMethod(this.dipatchMsgSubsignature);
			sm.addTag(new MyMethodTag(true));
		}
	}

	private void modifyChildOfHandler(SootClass childClass) {
		List<SootMethod> childMethods = childClass.getMethods();
		int orgSize = childMethods.size();
		List<SootMethod> newChildMths = new ArrayList<SootMethod>();
		for(SootMethod hm : Scene.v().getSootClass("android.os.Handler").getMethods()){	//all methods changed.
			boolean exist = false;
			for(SootMethod sm : childMethods)
				if(sm.getSubSignature().equals(hm.getSubSignature())){
					exist = true;
					break;
				}
			if(exist)	//the method is extended by child.
				continue;
			SootMethod newcm = new SootMethod(hm.getName(), hm.getParameterTypes(), hm.getReturnType());
			childClass.addMethod(newcm);
			Body hmBody = hm.retrieveActiveBody();
			if(hmBody == null)
				continue;
			Body cmBody = (Body) hmBody.clone();
			newcm.setActiveBody(cmBody);
			newChildMths.add(newcm);
		}
		
		int index = 0;
		childMethods = childClass.getMethods();	//re-get the methods list.
		while(index < orgSize){	//Original children methods. change the this references and do cg/cfg update. 
			if(modifyThisRefs(childMethods.get(index), childClass, false) && iCfg != null)	//call graph will be updated dynamically. return true mean the statements have been changed.
				iCfg.notifyMethodChanged(childMethods.get(index));	//update cfg
			index++;
		}
		while(index < childMethods.size()){	//copied from Handler class.
			modifyThisRefs(childMethods.get(index), childClass, true);	//call graph will not be updated dynamically
			notifyCGofNewMethod(childMethods.get(index));	//notify all new added method invocations to cg.
			if(iCfg != null)
				iCfg.notifyMethodChanged(childMethods.get(index));
//			SootMethod target = this. TODO
			index++;
		}
		if(handlerChildren.indexOf(childClass) < 0)
			handlerChildren.add(childClass);
	}

	/**@param isAdded, if it is false, when the replacement happened, we should notify the call graph*/
	private boolean modifyThisRefs(SootMethod mth, SootClass cls, boolean isAdded) {
		if(!mth.hasActiveBody())
			return false;
		Body body = mth.getActiveBody();
		if(body == null)
			return false;
		Stmt firstStmt = (Stmt) body.getUnits().getFirst();
		if(firstStmt == null)
			return false;
		
		Local thisLocal = null;
		try{thisLocal = body.getThisLocal();}catch(Exception e){}
		if(thisLocal == null)
			return false;
		thisLocal.setType(cls.getType());
		if((firstStmt instanceof IdentityUnit) && 
				((IdentityUnit)firstStmt).getLeftOp().equals(thisLocal)){
			((IdentityUnit)firstStmt).getRightOpBox().setValue(Jimple.v().newThisRef(cls.getType()));
		}
		
		for(Unit unit : mth.getActiveBody().getUnits()){
			for(ValueBox box : unit.getUseAndDefBoxes()){
				Value val = box.getValue();
				System.out.println(String.format("Box: %s. Value: %s", box.toString(), val.getClass().getName()));
				if(val instanceof InstanceInvokeExpr){
					InstanceInvokeExpr iie = (InstanceInvokeExpr)val;
					Value base = iie.getBase();
					if(!base.equals(thisLocal))
						continue;
					if(!iie.getMethod().getDeclaringClass().equals(Scene.v().getSootClass("android.os.Handler")))
						continue;
					String subSig = iie.getMethod().getSubSignature();
					SootMethod substitute = cls.getMethod(subSig);
					iie.setMethodRef(substitute.makeRef());
					
					if(isAdded)	//no need to notify the cg. because all the invoke stmt will be taken cared well later.
						continue;
					
					Iterator<Edge> edges = cg.edgesOutOf(unit);
					while(edges.hasNext()){
						Edge e = edges.next();
						e.setTgt(substitute);
					}
				}
			}
		}
		return true;
	}

	private void notifyCGofNewMethod(SootMethod newcm) {
		if(cg == null)
			return;
		for(Unit caller : newcm.getActiveBody().getUnits()){
			Stmt callStmt = (Stmt)caller;
			if(!callStmt.containsInvokeExpr())
				continue;
			Edge edge = new Edge(newcm, callStmt, callStmt.getInvokeExpr().getMethod());
				cg.addEdge(edge);
		}
	}

	private void patchMultiThreadClasses() {
		// learn from MyMultiThreadPatcher
		logger.info("PATCHING android.os.Handler!");
		patchHandler();
		logger.info("PATCHING java.lang.Thread!");
		patchThread();
		logger.info("***PATCHING of Multi-Thread Methods Finished!***");
	}
	
	/**
	 * Creates a synthetic minimal implementation of the java.lang.Thread class
	 * to model threading correctly even if we don't have a real implementation.
	 */
	private void patchThread() {
		SootClass sc = Scene.v().forceResolve("java.lang.Thread", SootClass.BODIES);
		if(sc == null || sc.isPhantom())
			return;
		
		SootMethod smRun = sc.getMethodUnsafe("void run()");
		if (smRun == null || smRun.hasActiveBody())
			return;

		SootClass runnable = Scene.v().forceResolve("java.lang.Runnable", SootClass.BODIES);
		if(runnable == null || runnable.isPhantom())
			return;
		
		// Create a field for storing the runnable
		int fieldIdx = 0;
		SootField fldTarget = null;
		while ((fldTarget = sc.getFieldByNameUnsafe("target" + fieldIdx)) != null)
			fieldIdx++;
		fldTarget = new SootField("target" + fieldIdx, runnable.getType());
		sc.addField(fldTarget);
		// Create a new constructor
		for(SootMethod sm : sc.getMethods()){
			if(!sm.getName().equals("<init>"))
				continue;
			if (sm == null || sm.hasActiveBody())
				return;
			List<Type> typeList = sm.getParameterTypes();
			if(typeList == null || typeList.isEmpty())
				continue;
			boolean hasRunableParam = false;
			int count = 0;
			for(Type type : typeList){
				if(type.toString().equals("java.lang.Runnable")){
					hasRunableParam = true;
					break;
				}
				count++;
			}
			if(!hasRunableParam)
				continue;
			patchThreadInit(sm, runnable, fldTarget, count);
			if(Options.v().debug())
				System.out.println("[KM] " + sm.getSignature() + "\n" + sm.getActiveBody());
		}
		// Create a new Thread.start() method
		patchThreadRun(smRun, runnable, fldTarget);
		if(Options.v().debug())
			System.out.println("[KM] " + smRun.getSignature() + "\n" + smRun.getActiveBody());
	}
	
	/**
	 * Creates a synthetic "java.lang.Thread.run()" method implementation that
	 * calls the target previously passed in when the constructor was called
	 * @param smRun The run() method for which to create a synthetic
	 * implementation
	 * @param runnable The "java.lang.Runnable" interface
	 * @param fldTarget The field containing the target object
	 */
	private void patchThreadRun(SootMethod smRun, SootClass runnable,
			SootField fldTarget) {
		SootClass sc = smRun.getDeclaringClass();
		Body b = Jimple.v().newBody(smRun);
		smRun.setActiveBody(b);
		
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		Local targetLocal = Jimple.v().newLocal("target", runnable.getType());
		b.getLocals().add(targetLocal);
		b.getUnits().add(Jimple.v().newAssignStmt(targetLocal,
				Jimple.v().newInstanceFieldRef(thisLocal, fldTarget.makeRef())));
		
		Unit retStmt = Jimple.v().newReturnVoidStmt();
		
		// If (this.target == null) return;
		b.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newEqExpr(targetLocal,
				NullConstant.v()), retStmt));
		
		// Invoke target.run()
		b.getUnits().add(Jimple.v().newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(targetLocal,
				runnable.getMethod("void run()").makeRef())));
		
		b.getUnits().add(retStmt);
	}
	
	/**
	 * Creates a synthetic "<init>(java.lang.Runnable)" method implementation
	 * that stores the given runnable into a field for later use
	 * @param smCons The <init>() method for which to create a synthetic
	 * implementation
	 * @param runnable The "java.lang.Runnable" interface
	 * @param fldTarget The field receiving the Runnable
	 * @param count 
	 */
	private void patchThreadInit(SootMethod smCons, SootClass runnable,
			SootField fldTarget, int targetCount) {
		SootClass sc = smCons.getDeclaringClass();
		Body b = Jimple.v().newBody(smCons);
		smCons.setActiveBody(b);
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		int count = 0;
		for(Type type : smCons.getParameterTypes()){
			Local paramLocal = Jimple.v().newLocal("p" + count, type);
			b.getLocals().add(paramLocal);
			
			b.getUnits().add(Jimple.v().newIdentityStmt(paramLocal,
					Jimple.v().newParameterRef(type, count)));
			
			if(count == targetCount)
				b.getUnits().add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(thisLocal,
						fldTarget.makeRef()), paramLocal));
			
			count++;
		}
		
		b.getUnits().add(Jimple.v().newReturnVoidStmt());
		return;
	}
	
	private void patchHandler() {
		SootClass msgSC = Scene.v().forceResolve("android.os.Message", SootClass.BODIES);
		if(msgSC== null || msgSC.isPhantom())
			return;
		
		SootClass sc = Scene.v().forceResolve("android.os.Handler", SootClass.BODIES);
		if(sc == null || sc.isPhantom())
			return;
		
		SootClass runnable = Scene.v().forceResolve("java.lang.Runnable", SootClass.BODIES);
		if(runnable == null || runnable.isPhantom())
			return;
		
		SootMethod smPost = sc.getMethodUnsafe(
				"boolean post(java.lang.Runnable)");
		SootMethod smPostAtFrontOfQueue = sc.getMethodUnsafe(
				"boolean postAtFrontOfQueue(java.lang.Runnable)");
		SootMethod smPostAtTimeWithToken = sc.getMethodUnsafe(
				"boolean postAtTime(java.lang.Runnable,java.lang.Object,long)");
		SootMethod smPostAtTime = sc.getMethodUnsafe(
				"boolean postAtTime(java.lang.Runnable,long)");
		SootMethod smPostDelayed = sc.getMethodUnsafe(
				"boolean postDelayed(java.lang.Runnable,long)");
		
		if (smPost != null && !smPost.hasActiveBody())
			patchHandlerPost(smPost, runnable);
		if (smPostAtFrontOfQueue != null && !smPostAtFrontOfQueue.hasActiveBody())
			patchHandlerPost(smPostAtFrontOfQueue, runnable);
		if (smPostAtTime != null && !smPostAtTime.hasActiveBody())
			patchHandlerPost(smPostAtTime, runnable);
		if (smPostAtTimeWithToken != null && !smPostAtTimeWithToken.hasActiveBody())
			patchHandlerPost(smPostAtTimeWithToken, runnable);
		if (smPostDelayed != null && !smPostDelayed.hasActiveBody())
			patchHandlerPost(smPostDelayed, runnable);
		for(String str : sendMessageMethods){
			SootMethod smsendMSG = sc.getMethodUnsafe(str);
			if(smsendMSG != null && !smsendMSG.hasActiveBody())
				patchHandlerSendMSG(smsendMSG);
		}
		
		SootMethod smobtainMSG = sc.getMethodUnsafe("android.os.Message obtainMessage(int)");
		if(smobtainMSG != null && !smobtainMSG.hasActiveBody())
			patchHandlerObtainMSG(smobtainMSG);
	}
	
	private void patchHandlerObtainMSG(SootMethod smobtainMSG) {
		SootClass sc = smobtainMSG.getDeclaringClass();
		Body b = Jimple.v().newBody(smobtainMSG);
		smobtainMSG.setActiveBody(b);
		
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		Local paramWhat = Jimple.v().newLocal("what", smobtainMSG.getParameterType(0));
		b.getLocals().add(paramWhat);
		b.getUnits().add(Jimple.v().newIdentityStmt(paramWhat,
				Jimple.v().newParameterRef(smobtainMSG.getParameterType(0), 0)));
		
		SootClass msgSC = Scene.v().getSootClass("android.os.Message");
		SootMethod msgInit = msgSC.getMethod("void <init>()");
		Local result = Jimple.v().newLocal("result", RefType.v(msgSC));
		b.getLocals().add(result);
		
		NewExpr newExpr = Jimple.v().newNewExpr(RefType.v(msgSC));
		AssignStmt assignStmt = Jimple.v().newAssignStmt(result, newExpr);
		b.getUnits().add(assignStmt);
		
		SpecialInvokeExpr vInvokeExpr = Jimple.v().newSpecialInvokeExpr(result, msgInit.makeRef());
		b.getUnits().add(Jimple.v().newInvokeStmt(vInvokeExpr));
//		
		
		SootFieldRef whatFieldRef = msgSC.getFieldByName("what").makeRef();
		JInstanceFieldRef whatRef = new JInstanceFieldRef(result, whatFieldRef);
		b.getUnits().add(Jimple.v().newAssignStmt(whatRef, paramWhat));
		
		SootFieldRef targetFieldRef = msgSC.getFieldByName("target").makeRef();
		JInstanceFieldRef targetField = new JInstanceFieldRef(result, targetFieldRef);
		b.getUnits().add(Jimple.v().newAssignStmt(targetField, thisLocal));
		
		return;
	}
	
	/**Creates a new body for sendMessage in androis.os.Handler
	 * make it to directly call the handleMessage() method*/
	private void patchHandlerSendMSG(SootMethod method) {
		SootClass sc = method.getDeclaringClass();
		Body b = Jimple.v().newBody(method);
		method.setActiveBody(b);
		
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		Local firstPrmLocal = Jimple.v().newLocal("msg", method.getParameterType(0));	
		b.getLocals().add(firstPrmLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(firstPrmLocal, Jimple.v().newParameterRef(method.getParameterType(0), 0)));
		
		// Assign the parameters
		Local firstParam = null;
		for (int i = 1; i < method.getParameterCount(); i++)  {
			Local paramLocal = Jimple.v().newLocal("param" + i, method.getParameterType(i));
			b.getLocals().add(paramLocal);
			b.getUnits().add(Jimple.v().newIdentityStmt(paramLocal,
					Jimple.v().newParameterRef(method.getParameterType(i), i)));
			if (i == 0)
				firstParam = paramLocal;
		}
		
		SootMethod smhandlerMSG = sc.getMethodUnsafe(dipatchMsgSubsignature);
		
		b.getUnits().add(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(thisLocal, smhandlerMSG.makeRef(), firstPrmLocal)));
		
		Unit retStmt = Jimple.v().newReturnStmt(soot.jimple.IntConstant.v(1));
		b.getUnits().add(retStmt);
		return;
	}
	
	/**
	 * Creates a new body for one of the postXXX methods in android.os.Handler
	 * @param method The method for which to create the implementation
	 * @param runnable The java.lang.Runnable class
	 * @return The newly created body
	 */
	private Body patchHandlerPost(SootMethod method, SootClass runnable) {
		SootClass sc = method.getDeclaringClass();
		Body b = Jimple.v().newBody(method);
		method.setActiveBody(b);
		
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		// Assign the parameters
		Local firstParam = null;
		for (int i = 0; i < method.getParameterCount(); i++)  {
			Local paramLocal = Jimple.v().newLocal("param" + i, method.getParameterType(i));
			b.getLocals().add(paramLocal);
			b.getUnits().add(Jimple.v().newIdentityStmt(paramLocal,
					Jimple.v().newParameterRef(method.getParameterType(i), i)));
			if (i == 0)
				firstParam = paramLocal;
		}
			
		b.getUnits().add(Jimple.v().newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(firstParam,
				Scene.v().makeMethodRef(runnable, "run", Collections.<Type>emptyList(), VoidType.v(), false))));
		
		Unit retStmt = Jimple.v().newReturnStmt(IntConstant.v(1));
		b.getUnits().add(retStmt);
		if(Options.v().debug())
			System.out.println("[KM] " + method.getSignature() + "\n" + b.toString());
		return b;
	}

	private IEntryPointCreator setDummyEntryPoints() {
		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		IEntryPointCreator epc = new DefaultEntryPointCreator(MTAScene.v().getTargetList());
		Scene.v().setEntryPoints(Collections.singletonList(epc.createDummyMain()));
		return epc;
	}
	
	
	//****************Start do resolve!**********************
	public void doResolve(List<String> targets) {
		for(String str : targets)
			resolveMethod(str, 0);
		logger.info("[KM] Non-Phantom List size: {}. IncludeList size: {}. Analyzed methods count: {}", nonPhantomList.size(), includeList.size(), invokedMths.size() );
		return;
	}


	private SootClass resolveClass(String clsName, int clsDepth) {
if(clsName.equals("com.kame.tafhd.MainActivity$AnotherHandler"))
	clsName.toString();
		if(clsDepth > MAX_CLASS_RESOLVE_DEPTH){
			SootClass rt = Scene.v().getSootClassUnsafe(clsName);
			if(rt == null){
				rt = SootResolver.v().makeClassRef(clsName);
				rt.setPhantomClass();
			}
			return rt;
		}
		
		if(nonPhantomList.contains(clsName))
			return Scene.v().getSootClass(clsName);
		
		String pkgName = clsName.substring(0, clsName.lastIndexOf("."));
		if(clsName.startsWith("java.lang.") && !myBasicClassList.contains(clsName))
			return Scene.v().getSootClass(clsName);
		
		nonPhantomList.add(clsName);
		if(clsName.startsWith("com.android.server") || clsName.equals("android.os.Handler") || clsName.equals("java.lang.Thread") || 
				MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			includeList.add(clsName);
		
		SootClass targetSC = Scene.v().getSootClassUnsafe(clsName);
		if(targetSC == null)
			targetSC = Scene.v().forceResolve(clsName, SootClass.SIGNATURES);
		if(targetSC.isPhantom()){
			Scene.v().removeClass(targetSC);
			targetSC = Scene.v().forceResolve(clsName, SootClass.SIGNATURES);
		}
		if(targetSC.isPhantom())
			return targetSC;
		if(targetSC.hasSuperclass())
			targetSC.setSuperclass(resolveClass(targetSC.getSuperclass().getName(), clsDepth + 1));
		if(targetSC.hasOuterClass())
			targetSC.setOuterClass(resolveClass(targetSC.getOuterClass().getName(), clsDepth + 1));
		for(Object obj : targetSC.getInterfaces().toArray()){
			SootClass interfaceCls = (SootClass) obj;
			SootClass newCls = resolveClass(interfaceCls.getName(), clsDepth + 1);
			if(newCls != null && !newCls.isPhantom()){
				targetSC.getInterfaces().remove(interfaceCls);
				targetSC.addInterface(newCls);
			}
		}
		
		if(MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			targetSC.setApplicationClass();
		
		if(targetSC.hasSuperclass() && targetSC.getSuperclass().equals(Scene.v().getSootClass("android.os.Handler")))
			modifyChildOfHandler(targetSC);
		return targetSC;
	}
	
	private SootMethod resolveMethod(String mthSig, int mthDepth) {
		SootMethod exist = null;
		try{exist = Scene.v().getMethod(mthSig);}catch(Exception e){}
		
		if(mthDepth > MAX_METHOD_RESOLVE_DEPTH){
			invokedMths.add(mthSig);
			return exist;
		}
			
		if(invokedMths.contains(mthSig))
			return exist;
		
		String clsName = mthSig.substring(1, mthSig.indexOf(":"));
		SootClass sc = Scene.v().getSootClassUnsafe(clsName);
		if(sc == null)
			sc = resolveClass(clsName, 0);
		else if(sc.isPhantom())
			Scene.v().removeClass(sc);
		
		if(sc.resolvingLevel() < SootClass.BODIES)
			Scene.v().forceResolve(sc.getName(), SootClass.BODIES);
		if(sc.isPhantom())
			return exist;
		
		String subSig = mthSig.substring(mthSig.indexOf(":") + 2, mthSig.length() - 1);
		SootMethod sm = sc.getMethodUnsafe(subSig);
		if(sm == null)
			return exist;
		if(!sm.hasActiveBody()){
			try{
				sm.retrieveActiveBody();
				assert !sm.isPhantom();
			}catch(Exception e){
				invokedMths.add(mthSig);
				return exist;
			}
		}
		
		invokedMths.add(mthSig);
		if(!sm.hasActiveBody())
			return exist;
		
//		updata CFG
System.out.println("[BEFORE] " + sm.getSignature() + "\n" + sm.getActiveBody().toString());
		CallGraphManager.optimizeCG(sm.getActiveBody());
System.out.println("[AFTER] " + sm.getSignature() + "\n" + sm.getActiveBody().toString());
//iCfg.notifyMethodChanged(sm);

		for(Unit unit : sm.getActiveBody().getUnits()){
			Stmt stmt = (Stmt)unit;
			for(ValueBox box : stmt.getUseAndDefBoxes()){
				Value val = box.getValue();
				Type type = val.getType();
				SootClass tgt = null;
				if(type instanceof RefType){
					tgt = resolveClass(((RefType)type).getSootClass().getName(), 0);
				}
			}
//			if(stmt.containsInvokeExpr()){
//				Collection<SootMethod> callees = iCfg.getCalleesOfCallAt(stmt);
//				Iterator<Edge> edges = cg.edgesOutOf(stmt);
//				ValueBox basebox = ((InstanceInvokeExpr)stmt.getInvokeExpr()).getBaseBox();
//				SootClass baseSC = ((RefType)basebox.getValue().getType()).getSootClass();
//				List<SootClass> superCls = Scene.v().getActiveHierarchy().getSuperclassesOf(baseSC);
////				List<SootClass> interCls = Scene.v().getActiveHierarchy().getSuperinterfacesOf(baseSC);
//				while(edges.hasNext()){
//					Edge e = edges.next();
//					SootMethod tgt = (SootMethod) e.getTgt();
//					SootClass orgSC = tgt.getDeclaringClass();
//					if(superCls.contains(orgSC)){	//we can update the call edges!  
//						
//					}
//				}
////				callees 不包含 basebox的情况！
//			}
		}
		
		iCfg.notifyMethodChanged(sm);

		for(Unit u : iCfg.getCallsFromWithin(sm)){	//get the invoke statement in one method. 
			Collection<SootMethod> callees = iCfg.getCalleesOfCallAt(u);
			if(callees.size() == 0){
				SootMethod callee = ((Stmt)u).getInvokeExpr().getMethod();
				callee.toString();
			}
			for(SootMethod cle : callees){
				SootMethod newcle = resolveMethod(cle.getSignature(), mthDepth + 1);
				Iterator<Edge> edges0 = cg.edgesOutOf(u);
				if(newcle != null && newcle != cle){
					// the callee has been updated. we should modify the cg and cfg for next test.
					InvokeExpr ie = ((Stmt)u).getInvokeExpr();
					ie.setMethodRef(newcle.makeRef());
					Iterator<Edge> edges = cg.edgesOutOf(u);
					while(edges.hasNext()){
						Edge e = edges.next();
						e.setTgt(newcle);
					}
					iCfg.notifyMethodChanged(sm);
				}
			}
		}
		
		return sm;
	}

	private boolean isExceptionChild(SootClass target) {
		SootClass objClass = Scene.v().getSootClass("java.lang.Object");
		SootClass excClass = Scene.v().getSootClass("java.lang.Exception");
		while(!target.equals(objClass)){
			if(target.equals(excClass))
				return true;
			if(!target.hasSuperclass())
				return false;
			target = target.getSuperclass();
		}
		return false;
	}
}
