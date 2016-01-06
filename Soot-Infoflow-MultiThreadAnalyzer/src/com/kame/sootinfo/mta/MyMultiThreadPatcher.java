package com.kame.sootinfo.mta;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import soot.Body;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.AssignStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.infoflow.cfg.LibraryClassPatcher;
import soot.jimple.internal.JInstanceFieldRef;
import soot.options.Options;

/**soot-info���ṩ��LibraryClassPatcherʵ���˶��ڼ򵥵�Thread��Handler���ƵĲ��䣬�����Ⲣ���㹻����Ҫ���ǽ�һ�����й�����ǿ*/
public class MyMultiThreadPatcher {
	/**
	 * Patches all supported system libraries
	 */
	public void patchLibraries() {
		if(Options.v().debug())
			System.out.println("[KM] PatchLibraries: Thread & Handler");
		
		
        // Patch the java.lang.Thread implementation
		patchHandlerImplementation();
		
		// Patch the android.os.Handler implementation
		patchThreadImplementation();
		
//		pathcMessageImplementation();
	}
	
//	private void pathcMessageImplementation() {
//		SootClass sc = Scene.v().forceResolve("android.os.Message", SootClass.BODIES);
//		
//	}

	/**
	 * Creates a synthetic minimal implementation of the java.lang.Thread class
	 * to model threading correctly even if we don't have a real implementation.
	 */
	private void patchThreadImplementation() {
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
		
//		SootMethod smCons = sc.getMethodUnsafe("void <init>(java.lang.Runnable)");
//		if (smCons == null || smCons.hasActiveBody())
//			return;
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
			patchThreadConstructor(sm, runnable, fldTarget, count);
			if(Options.v().debug())
				System.out.println("[KM] " + sm.getSignature() + "\n" + sm.getActiveBody());
		}
		
		
		// Create a new Thread.start() method
		patchThreadRunMethod(smRun, runnable, fldTarget);
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
	private void patchThreadRunMethod(SootMethod smRun, SootClass runnable,
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
	private void patchThreadConstructor(SootMethod smCons, SootClass runnable,
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
	
	/**
	 * Creates a dummy implementation of android.os.Handler if we don't have one
	 */
	private void patchHandlerImplementation() {
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
			patchHandlerPostBody(smPost, runnable);
		if (smPostAtFrontOfQueue != null && !smPostAtFrontOfQueue.hasActiveBody())
			patchHandlerPostBody(smPostAtFrontOfQueue, runnable);
		if (smPostAtTime != null && !smPostAtTime.hasActiveBody())
			patchHandlerPostBody(smPostAtTime, runnable);
		if (smPostAtTimeWithToken != null && !smPostAtTimeWithToken.hasActiveBody())
			patchHandlerPostBody(smPostAtTimeWithToken, runnable);
		if (smPostDelayed != null && !smPostDelayed.hasActiveBody())
			patchHandlerPostBody(smPostDelayed, runnable);
		
		SootMethod smsendMSG = sc.getMethodUnsafe("boolean sendMessage(android.os.Message)");
		if(smsendMSG != null && !smsendMSG.hasActiveBody())
			patchHandlerSendMSGBody(smsendMSG);
		
		SootMethod smobtainMSG = sc.getMethodUnsafe("android.os.Message obtainMessage(int)");
		if(smobtainMSG != null && !smobtainMSG.hasActiveBody())
			patchHandlerObtainMSGBody(smobtainMSG);
	}
	
	private void patchHandlerObtainMSGBody(SootMethod smobtainMSG) {
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
		
//        $r1 = new com.kame.tafhd.MainActivity;
//        specialinvoke $r1.<com.kame.tafhd.MainActivity: void <init>()>();
		SootClass msgSC = Scene.v().getSootClass("android.os.Message");
		SootMethod msgInit = msgSC.getMethod("void <init>()");
		Local result = Jimple.v().newLocal("result", RefType.v(msgSC));
		b.getLocals().add(result);
		
		NewExpr newExpr = Jimple.v().newNewExpr(RefType.v(msgSC));
//		Local tempLocal = new LocalGenerator(b).generateLocal(RefType.v(msgSC));			
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
	private void patchHandlerSendMSGBody(SootMethod smsendMSG) {
		SootClass sc = smsendMSG.getDeclaringClass();
		Body b = Jimple.v().newBody(smsendMSG);
		smsendMSG.setActiveBody(b);
		
		Local thisLocal = Jimple.v().newLocal("this", sc.getType());
		b.getLocals().add(thisLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(thisLocal,
				Jimple.v().newThisRef(sc.getType())));
		
		Local paramLocal = Jimple.v().newLocal("msg", smsendMSG.getParameterType(0));
		b.getLocals().add(paramLocal);
		b.getUnits().add(Jimple.v().newIdentityStmt(paramLocal,
					Jimple.v().newParameterRef(smsendMSG.getParameterType(0), 0)));
		
		SootMethod smhandlerMSG = sc.getMethodUnsafe("void handleMessage(android.os.Message)");
		
		b.getUnits().add(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(thisLocal, smhandlerMSG.makeRef(), paramLocal)));
		
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
	private Body patchHandlerPostBody(SootMethod method, SootClass runnable) {
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
}
