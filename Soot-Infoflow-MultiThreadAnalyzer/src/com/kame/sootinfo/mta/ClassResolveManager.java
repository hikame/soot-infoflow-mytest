package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.tags.MyMethodTag;

import soot.ArrayType;
import soot.Body;
import soot.ClassSource;
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
import soot.SootMethodRef;
import soot.SootResolver;
import soot.SourceLocator;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.javaToJimple.IInitialResolver.Dependencies;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
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
	List<String> nonPhantomClasses = new ArrayList<String>();
	List<String> failedClasses = new ArrayList<String>();
	List<String> resolvedMths = new ArrayList<String>();
	List<String> failedMths = new ArrayList<String>();
	public List<String> getResolvedMethods(){
		return resolvedMths;
	}
	
	List<String> myBasicClassList = null;
	{
		String[] myBasicClassSet = {
			"java.lang.Object",
			"java.lang.Runnable",
			"java.lang.Thread",
			"java.lang.Throwable",
			"java.lang.Exception",
			//this are learned from List<SootMethod> soot.EntryPoints.implicit()
			"java.lang.System",
			"java.lang.ThreadGroup",
			"java.lang.ClassLoader",
			"java.security.PrivilegedActionException",
			"java.lang.ref.Finalizer",
			"java.util.AbstractList",
			"java.util.List",
			"java.util.TreeMap",
			//**********
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

	Map<SootMethod, Integer> interfaceInvokeMap = new HashMap<SootMethod, Integer>();
	Stack<SootMethod> interfaceInvokeStack = new Stack<SootMethod>();

	public SootMethod extendResolving(String methodName, int level){
		SootMethod result = resolveMethod(methodName, MAX_METHOD_RESOLVE_DEPTH / 2);
		assertAllAbove(level);
		return result;
	}
	
	/**It should be able to dynamically extend the include&nonPhantom lists.
	 * And at the same time, generate&extend the control flow graph*/
	public void start(){
		Options.v().set_include(includeList);
		Options.v().set_exclude(excludeList);
		Options.v().set_nonPhantom(nonPhantomClasses);
		for(String s: myBasicClassList){
			resolveClass(s, SootClass.BODIES);
		}
		Scene.v().loadBasicClasses();
		Scene.v().loadNecessaryClasses(); //load some missing neccesary classes. 
		patchMultiThreadClasses();	//taking care of thread.start handler.post handler.send message.sendtotarget and so on.

		for(SootMethod sm : Scene.v().getSootClass("android.os.Handler").getMethods())
			resolveMethod(sm.getSignature(), 0);	//resolve all the methods belonging to android.os.Handler
		//Set MyMethodTag to be true to mark the method of dipatchMsg() to be multi-thread.
		Scene.v().getSootClass("android.os.Handler").getMethod(dipatchMsgSubsignature).addTag(new MyMethodTag(true));
		
		Map<String, Set<String>> classMap =
				SootMethodRepresentationParser.v().parseClassNames(MTAScene.v().getTargetList(), false);
		for(String clsname : classMap.keySet()){	//Resolve be base class of target method.
			Scene.v().addBasicClass(clsname, SootClass.BODIES);
			SootClass cls = resolveClass(clsname, SootClass.BODIES);
			for (SootMethod method : cls.getMethods()) {	//parse init method
				if (method.isConstructor() || method.isStaticInitializer()){
					resolveMethod(method.getSignature(), 0);	//TODO is this suitable
//					method.setPhantom(true);
				}
			}
			for(String method : classMap.get(clsname)){		//parse target method
				resolveMethod(method, 0);	//change cg/iCfg and then immediately use it!
			}
		}
		setDummyEntryPoints();	//generate the dummy main method.
		List<SootMethod> eps = Scene.v().getEntryPoints();
		for(SootMethod entryMethod : eps){
			SootClass sc = entryMethod.getDeclaringClass();	//it is born to be body-level.
			for(SootMethod sm : sc.getMethods())
				resolveMethod(sm.getSignature(), 0); //they are resolved in case of missing something. WHAT'S MORE, it will update the cg/cfg
		}
		
//		while(!interfaceInvokeStack.isEmpty()){
//			SootMethod intMth = interfaceInvokeStack.pop();
//			int depth = interfaceInvokeMap.get(intMth);
//			List<String> implementers = getImplementers(intMth);
//			System.out.println("[Interface Analyze] Interface: " + intMth.getSignature());
//			for(String sig : implementers){
//				System.out.println("[Interface Analyze] -> Implementer: " + sig);
//				resolveMethod(sig, depth);
//			}
//		}
//TODO release the private created classes in privateClassMap and remove their un-resolve super/interfaces/outer
		assertAllAbove(SootClass.SIGNATURES);
	}

	private void assertAllAbove(int level) {
		List<SootClass> toResolveList = null;
		while((toResolveList = getClassesBelow(level)).size() > 0)
			for(SootClass sc : toResolveList){
				if(Options.v().debug_resolver())
					System.out.println(String.format("Assert class(%s) to target level - %d", sc.getName(), level));
				sc.setPhantomClass();
				sc.setResolvingLevel(level);
				for(SootMethod sm : sc.getMethods())
					sm.setPhantom(true);
			}
		return;
	}
	private Map<String, SootClass> privateClassMap = new HashMap<String, SootClass>();
	private List<String> getImplementers(SootMethod intMth) {
		List<String> result = new ArrayList<String>();
		String interfaceName = intMth.getDeclaringClass().getName();
		String subSig = intMth.getSubSignature();
		
		for(SootClass sc : Scene.v().getClasses().toArray(new SootClass[0])){
			if(sc.getName().equals(interfaceName))
				continue;
			sc = getNonPhantomClass(sc);
			if(sc == null)
				continue;
			SootMethod sm = sc.getMethodUnsafe(subSig);
			if(sm == null)	//this method has not implement the target method
				continue;
			//check whether the class implements the interface
			if(checkInterface(sc, interfaceName))
				result.add(sm.getSignature());
		}
		
		return result;
	}

	private SootClass getNonPhantomClass(SootClass sc) {
		if(!sc.isPhantom())
			return sc;
		SootClass substitution = null;
		if(privateClassMap.containsKey(sc.getName()))
			return 	privateClassMap.get(sc.getName());
		substitution = new SootClass(sc.getName(), 0, true);
		Dependencies depends = doPrivateResolve(substitution);
		if(depends == null){
			privateClassMap.put(sc.getName(), null);
			return null;
		}
		substitution.setResolvingLevel(SootClass.HIERARCHY);
		privateClassMap.put(sc.getName(), substitution);
		return substitution;
	}

	private boolean checkInterface(SootClass sc, String interfaceName) {
		while(true){
			if(sc.implementsInterface(interfaceName))	//check sc itserlf
				return true;
			for(SootClass si : sc.getInterfaces()){	//check every sub-interface
				si = getNonPhantomClass(si);
				if(si == null)
					continue;
				while(true){
					if(si.getName().equals(interfaceName))	//the interface name is correct
						return true;
					if(si.hasSuperclass()){	//the interface extends some basic interface
						si = getNonPhantomClass(si.getSuperclass());
						if(si == null)
							break;
					}
					else	//there is no more super interfaces, we should break the loop.
						break;
				}
			}
			if(sc.hasSuperclass()){	//check superclass.
				sc = getNonPhantomClass(sc.getSuperclass());
				if(sc == null)
					break;
			}
			else
				break;
		}
		return false;
	}

	private Dependencies doPrivateResolve(SootClass substitution) {
		ClassSource is = SourceLocator.v().getClassSource(substitution.getName());
		if(is == null)
			return null;
		Dependencies depends = is.resolve(substitution);
		return depends;
	}

	private List<SootClass> getClassesBelow(int level) {
		List<SootClass> result = new ArrayList<SootClass>();
		for(SootClass sc : Scene.v().getClasses()){
			if(sc.resolvingLevel() < level)
				result.add(sc);
		}
		return result;
	}

	private void modifyChildOfHandler(SootClass childClass) {
		if(handlerChildren.contains(childClass))
			return;
		childClass = SootResolver.v().resolveClass(childClass.getName(), SootClass.BODIES);
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
			if(hm.isPhantom())	//in case hm.retrieveActiveBody(); failed
				hm.setPhantom(false);
			if(!hm.hasActiveBody())
				continue;
			Body hmBody = hm.getActiveBody();
			Body cmBody = (Body) hmBody.clone();
			newcm.setActiveBody(cmBody);
			newChildMths.add(newcm);			
		}
		
		int index = 0;
		childMethods = childClass.getMethods();	//re-get the methods list.
		while(index < orgSize){	//Original children methods. change the this references and do cg/cfg update. 
			modifyThisRefs(childMethods.get(index), childClass, false);
			index++;
		}
		while(index < childMethods.size()){	//copied from Handler class.
			modifyThisRefs(childMethods.get(index), childClass, true);	//call graph will not be updated dynamically
			index++;
		}
		
		if(handlerChildren.indexOf(childClass) < 0)
			handlerChildren.add(childClass);
		
		SootMethod dispatchMethod = childClass.getMethod(this.dipatchMsgSubsignature);
		dispatchMethod = resolveMethod(dispatchMethod.getSignature(), 0);	//make the resolving depth starting from dispatchMessage to be right.
		if(dispatchMethod != null)
			dispatchMethod.addTag(new MyMethodTag(true));
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
					
//					Iterator<Edge> edges = cg.edgesOutOf(unit);
//					while(edges.hasNext()){
//						Edge e = edges.next();
//						e.setTgt(substitute);
//					}
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
		
		b.getUnits().add(Jimple.v().newReturnStmt(result));
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
	
	private SootClass resolveClass(String clsName, int level) {
		SootClass result = Scene.v().getSootClassUnsafe(clsName);
		if(result != null && result.isPhantom()){	//the phantom situation
			if(failedClasses.contains(clsName)){	//it has been resolved, but failed. It is a nature phantom class.
				result.setResolvingLevel(level);
				return result;
			}
			Scene.v().removeClass(result);	//remove and perpare for re-resolve
			result = null;
		}
		
		if(result != null && result.resolvingLevel() > level)
			return result;
		
//		if(clsName.startsWith("java.lang.") && !myBasicClassList.contains(clsName)){	//java.lang.* may not 
//			failedClasses.add(clsName);
//			return Scene.v().forceResolve(clsName, SootClass.BODIES);	//Let's make it phantom
//		}
			
		if(!nonPhantomClasses.contains(clsName))	//prepare for resolving
			nonPhantomClasses.add(clsName);
		result = Scene.v().forceResolve(clsName, level);
		if(result.isPhantom())	//it is a nature phantom class.
			failedClasses.add(clsName);
		
		String pkgName = clsName.contains(".") ? 
				clsName.substring(0, clsName.lastIndexOf(".")) : "";
		if(clsName.startsWith("com.android.server") || 
				clsName.equals("android.os.Handler") || 
				clsName.equals("java.lang.Thread") || 
				MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			includeList.add(clsName);	//TODO is it suitable?
		
		if(MTAScene.v().getTargetList().get(0).startsWith("<" + pkgName))
			result.setApplicationClass();
		
		if(result.hasSuperclass() && result.getSuperclass().equals(Scene.v().getSootClass("android.os.Handler")))
			modifyChildOfHandler(result);
		return result;
	}
	
	private SootMethod resolveMethod(String mthSig, int mthDepth) {
		SootMethod result = null;
		String clsName = mthSig.substring(1, mthSig.indexOf(":"));
		String subSignature = mthSig.substring(mthSig.indexOf(": ") + 2, mthSig.length() - 1);
		SootClass baseClass = null;
		while(result == null){
			baseClass = resolveClass(clsName, SootClass.SIGNATURES);	//try to find the real base class
			result = baseClass.getMethodUnsafe(subSignature);
			if(!baseClass.hasSuperclass())
				break;
			clsName = baseClass.getSuperclass().getName();
		}
		
		if(result == null)
			return null;
		
		if(resolvedMths.contains(mthSig) || failedMths.contains(mthSig))	//if it has been resolved before, return directly.
			return result;
		
		if(mthDepth > MAX_METHOD_RESOLVE_DEPTH){	//if it has surpassed the max depth, also since it reaches here, it means that this is the first arriver.
			//TODO make sure setPhantom(true) will not erase the body.
			result.setPhantom(true);	//will not add the method into the resovledMths list. therefore, next time the same mthSig arrived and the depth is not more the max, the resolve will continue normally.
//			result.releaseActiveBody(); //if it is used later, the codes will reconstruct it.(WRONG!!! nonono, one get body, it could not be parsed again!)
			return result;	
		}
		
		if(baseClass.isPhantom()){
			failedMths.add(mthSig);
			return result;
		}
		baseClass = resolveClass(baseClass.getName(), SootClass.BODIES);	//we need to resolve it normally.
		result = baseClass.getMethod(result.getSubSignature());
		
		if(result.isPhantom())	//the method has arrived the max depth before! But here it is not!
			result.setPhantom(false);
		
		if(!result.hasActiveBody()){
			Type returnType = result.getReturnType();
			resolveFromType(returnType, SootClass.SIGNATURES);	//just in case
			for(Type paramType : result.getParameterTypes())
				resolveFromType(paramType, SootClass.SIGNATURES);	//just in case
			try{result.retrieveActiveBody();}catch(Exception e){result.setPhantom(true);}
		}
		if(!result.hasActiveBody()){
			failedMths.add(mthSig);	//we can not get the method body!
//			result.setPhantom(true);TODO!!!!!!!!!!!!!!!!!!!!
			return result;
		}
		
		resolvedMths.add(mthSig);
		//optimize method body and updata CFG
		CallGraphManager.optimizeCG(result.getActiveBody());
		
		for(Trap trap : result.getActiveBody().getTraps())	//Exception handler
			resolveClass(trap.getException().getName(), SootClass.BODIES);
		
		for(Unit unit : result.getActiveBody().getUnits()){
			Stmt stmt = (Stmt)unit;
			for(ValueBox box : stmt.getUseAndDefBoxes()){
				Value val = box.getValue();
				//ref & local
				if((val instanceof ParameterRef) || (val instanceof Local)){
					Type type = val.getType();
					resolveFromType(type, SootClass.HIERARCHY);
				}
				else if(val instanceof FieldRef){
					FieldRef fr = (FieldRef) val;
					SootClass sc = fr.getFieldRef().declaringClass();
					if(sc.resolvingLevel() < 3)
						resolveClass(sc.getName(), SootClass.BODIES);
					if(fr.getField().isStatic())
						resolveClinitMethod(sc.getName(), mthDepth + 1);
					else
						resolveClass(sc.getName(), SootClass.BODIES);
				}
				else if(val instanceof ArrayRef){
					Type type = ((ArrayRef)val).getBase().getType();
					resolveFromType(type, SootClass.HIERARCHY);
				}
				//expr
				else if(val instanceof NewExpr)
					resolveClinitMethod(((NewExpr)val).getBaseType().getClassName(), mthDepth + 1);
				else if(val instanceof CastExpr){
					Type castType = ((CastExpr)val).getCastType();
					resolveFromType(castType, SootClass.BODIES);
				}else if(val instanceof InstanceOfExpr){
					Type checkType = ((InstanceOfExpr)val).getCheckType();
					resolveFromType(checkType, SootClass.BODIES);
				}else if(val instanceof NewArrayExpr){
					Type baseType = ((NewArrayExpr)val).getBaseType();
					resolveFromType(baseType, SootClass.BODIES);
				}else if(val instanceof NewMultiArrayExpr){
					Type baseType = ((NewMultiArrayExpr)val).getBaseType();
					resolveFromType(baseType, SootClass.BODIES);
				}
				else if(val instanceof InvokeExpr){
					InvokeExpr ie = (InvokeExpr) val;
					SootMethodRef methodref = stmt.getInvokeExpr().getMethodRef();
					SootClass sc = methodref.declaringClass();
					if(sc.resolvingLevel() < SootClass.BODIES)
						resolveClass(sc.getName(), SootClass.BODIES);
					SootMethod callee =	stmt.getInvokeExpr().getMethod();
//					if(val instanceof InterfaceInvokeExpr){//must be handled
//						if(interfaceInvokeMap.containsKey(callee)){
//							int orgDpt = interfaceInvokeMap.get(callee);
//							if(orgDpt > mthDepth)	//the new depth is shorter.
//								interfaceInvokeMap.put(callee, mthDepth);
//						}else{
//							interfaceInvokeStack.push(callee);
//							interfaceInvokeMap.put(callee, mthDepth);
//						}
//					}
					if(val instanceof StaticInvokeExpr)
						resolveClinitMethod(callee.getDeclaringClass().getName(), mthDepth + 1);
					SootMethod newcle = resolveMethod(callee.getSignature(), mthDepth + 1);
					if(newcle != null && newcle != callee){
						ie.setMethodRef(newcle.makeRef());
					}
				}
			}
		}
		return result;
	}

	private void resolveClinitMethod(String clsName, int depth) {
		SootClass bc = resolveClass(clsName, SootClass.SIGNATURES);	//if it hase <clinit> method resolveMethod() will resolve the class to bodies level
		SootMethod clinit = bc.getMethodUnsafe("void <clinit>()");
		if(clinit != null)
			resolveMethod(clinit.getSignature(), depth);
	}

	private void resolveFromType(Type type, int level) {
		if(type instanceof ArrayType)
			type = ((ArrayType)type).getElementType();
		if(type instanceof RefType)
			resolveClass(((RefType)type).getSootClass().getName(), level);
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
