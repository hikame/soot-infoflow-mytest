package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


import soot.Body;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.util.Chain;

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

//	public List<String> getInvokedMethods(){
//		return invokedMths;
//	}
	
	String[] myBasicClass = {
		"java.lang.Thread",
		"java.lang.Throwable",
		"android.os.Handler",
		"android.os.Message",
		"java.lang.Runnable"
	};
	
	String[] sendMessageMethods = {
		"boolean sendMessage(android.os.Message)",
		"boolean sendMessageAtFrontOfQueue(android.os.Message)",
		"boolean sendMessageAtTime(android.os.Message,long)",
		"boolean sendMessageDelayed(android.os.Message,long)"	
	};
	private SootClass handlerClass = null;

//void myTest(){
//	SootMethod disMsg = Scene.v().getMethod("<android.os.Handler: void dispatchMessage(android.os.Message)>");
//	Collection<Unit> calls = ControlFlowGraphManager.v().getInfoflowCFG().getCallsFromWithin(disMsg);
//	for(Unit u : calls){
//		if(u.toString().equals("virtualinvoke this.<android.os.Handler: void handleMessage(android.os.Message)>(msg)")){
////			Collection<SootMethod> inter = ControlFlowGraphManager.v().getInfoflowCFG().getCalleesOfCallAt(u);
////			System.out.println(inter.toString().replace("),", ")\n"));
////			System.out.println("$$$");
//			Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(u);
//			while(edges.hasNext()){
//				System.out.println(edges.next());
//			}
//			System.out.println("$$$");
//		}
//	}
//}
	/**It should be able to dynamically extend the include&nonPhantom lists.
	 * And at the same time, generate&extend the control flow graph*/
	public void start(){
		Options.v().set_include(includeList);
		Options.v().set_exclude(excludeList);
		Options.v().set_nonPhantom(nonPhantomList);
		for(String s: myBasicClass){
			nonPhantomList.add(s);
			Scene.v().addBasicClass(s, SootClass.BODIES);
		}
		
		for(String s : MTAScene.v().getTargetList()){
			String clsName = s.substring(1, s.indexOf(":"));
			nonPhantomList.add(clsName);
			Scene.v().addBasicClass(s, SootClass.BODIES);
		}
		setDummyEntryPoints();
		
		Scene.v().loadBasicClasses();
		patchMultiThreadClasses();
		
		handlerClass = Scene.v().getSootClass("android.os.Handler");
		Chain<SootClass> resolvedClasses = Scene.v().getClasses();
		for(SootClass sc = resolvedClasses.getFirst(); resolvedClasses.getSuccOf(sc) != null; sc = resolvedClasses.getSuccOf(sc)){
			if(sc.isPhantom())
				continue;
			if(sc.hasSuperclass() && sc.getSuperclass().equals(handlerClass)){	//add all unimplemented bodys from Handler to SubHander;
				modifyChildOfHandler(sc);
			}
		}
		
		//���ڸո���ӵķ�������һ�γ�ʼ��CG��CFG����
		CallGraphManager.v().constructCallgraph();
		ControlFlowGraphManager.v().generateCFG();
		List<SootMethod> startPoints = Scene.v().getEntryPoints();
		assert startPoints.size() == 1;
		String startMethd = startPoints.get(0).getSignature();
		List<String> list = new ArrayList<String>();
		list.add(startMethd);
		doResolve(list);
		
		ControlFlowGraphManager.v().eliminateDeadCode(MTAScene.v().getSourceSinkManager());
	}

	private void modifyChildOfHandler(SootClass childClass) {
		List<SootMethod> childMethods = childClass.getMethods();
		for(SootMethod hm : handlerClass.getMethods()){
			boolean exist = false;
			for(SootMethod sm : childMethods)
				if(sm.getSubSignature().equals(hm.getSubSignature())){
					exist = true;
					break;
				}
			if(exist)	//the method is extended by child.
				continue;
//			if(childMethods.contains(hm))	//the method is extended by child.
//				continue;
			SootMethod newcm = new SootMethod(hm.getName(), hm.getParameterTypes(), hm.getReturnType());
			childClass.addMethod(newcm);
			Body hmBody = hm.retrieveActiveBody();
			Body cmBody = (Body) hmBody.clone();
			newcm.setActiveBody(cmBody);
		}
	}

	private void patchMultiThreadClasses() {
		// learn from MyMultiThreadPatcher
		patchHandler();
		patchThread();
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
		
//		android.os.Handler: sendMessageAtFrontOfQueue(android.os.Message)
//		android.os.Handler: sendMessageAtTime(android.os.Message, long)
//		android.os.Handler: sendMessageDelayed(android.os.Message, long)
		//�������ݸ�Ϊֱ��invokeHandler
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
//		b.getUnits().add(Jimple.v().newIdentityStmt(result, tempLocal));
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
		
		Local firstPrmLocal = Jimple.v().newLocal("msg", method.getParameterType(0));	//��һ������
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
		
		SootMethod smhandlerMSG = sc.getMethodUnsafe("void dispatchMessage(android.os.Message)");
		
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
			
		// Invoke p0.run()
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
		if(clsDepth > MAX_CLASS_RESOLVE_DEPTH || nonPhantomList.contains(clsName))
			return null;
		String pkgName = clsName.substring(0, clsName.lastIndexOf("."));
		if(clsName.startsWith("java.lang.") && !clsName.equals("java.lang.Thread"))
			return Scene.v().getSootClass(clsName);
		
		nonPhantomList.add(clsName);
		if(clsName.startsWith("com.android.server") || clsName.equals("android.os.Handler") || clsName.equals("java.lang.Thread") || 
				MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			includeList.add(clsName);
		SootClass targetSC = Scene.v().getSootClass(clsName);
		if(targetSC.isPhantom()){	//֮ǰ������һ��phantom���~
			Scene.v().removeClass(targetSC);
			targetSC = Scene.v().forceResolve(clsName, SootClass.SIGNATURES);
		}
		if(targetSC.isPhantom())
			return targetSC;
		if(targetSC.hasSuperclass())
			resolveClass(targetSC.getSuperclass().getName(), clsDepth + 1);
		if(targetSC.hasOuterClass())
			resolveClass(targetSC.getOuterClass().getName(), clsDepth + 1);
		for(SootClass interfaceCls : targetSC.getInterfaces())
			resolveClass(interfaceCls.getName(), clsDepth + 1);
		
		if(MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			targetSC.setApplicationClass();
		
		if(targetSC.hasSuperclass() && targetSC.getSuperclass().equals(handlerClass))
			modifyChildOfHandler(targetSC);
		return targetSC;
	}
	
	private void resolveMethod(String mthSig, int mthDepth) {
		if(mthDepth > MAX_METHOD_RESOLVE_DEPTH){
			invokedMths.add(mthSig);	//����ֻ�ǲ��������ݽ��������ļ��غ�CFG����չ��
			return;
		}
			
		if(invokedMths.contains(mthSig))
			return;
		
		String clsName = mthSig.substring(1, mthSig.indexOf(":"));
		SootClass sc = Scene.v().getSootClassUnsafe(clsName);
		if(sc == null)
			sc = resolveClass(clsName, 0);
		else if(sc.isPhantom())
			Scene.v().removeClass(sc);
		
		if(sc.resolvingLevel() < SootClass.BODIES)
			Scene.v().forceResolve(sc.getName(), SootClass.BODIES);
		String subSig = mthSig.substring(mthSig.indexOf(":") + 2, mthSig.length() - 1);
		SootMethod sm = sc.getMethodUnsafe(subSig);
		if(sm == null)
			return;
		if(!sm.hasActiveBody()){
			try{
				sm.retrieveActiveBody();
				assert !sm.isPhantom();
			}catch(Exception e){
				invokedMths.add(mthSig);
				return;
			}
		}
		
		invokedMths.add(mthSig);
		assert sm.hasActiveBody();
		
//		updata CFG
		IInfoflowCFG cfg = ControlFlowGraphManager.v().getInfoflowCFG();
		cfg.notifyMethodChanged(sm);
		//���õ���value�����е����õ�Java���������
		List<ValueBox> boxes = sm.getActiveBody().getUseAndDefBoxes();
		for(ValueBox box : boxes){
			Value value = box.getValue();
			Type type = value.getType();
			addTypeToLists(type);
		}
		
		//����������е��õķ��������������
		for(Unit u : cfg.getCallsFromWithin(sm)){
			Collection<SootMethod> callees = cfg.getCalleesOfCallAt(u);
			for(SootMethod cle : callees){
				resolveMethod(cle.getSignature(), mthDepth + 1);
			}
		}
	}

	private void addTypeToLists(Type type) {
		if(type instanceof RefType){
			SootClass sc = ((RefType) type).getSootClass();
			resolveClass(sc.getName(), 0);
		}
	}
}
