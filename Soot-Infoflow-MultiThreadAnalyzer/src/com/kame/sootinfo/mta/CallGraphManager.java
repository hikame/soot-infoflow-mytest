package com.kame.sootinfo.mta;

import java.lang.reflect.Field;
import java.util.Collection;
import java.util.Collections;

import kame.soot.UnresolvedClassException;
import soot.Body;
import soot.G;
import soot.Pack;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.jimple.InvokeExpr;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.cfg.LibraryClassPatcher;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.handlers.PreAnalysisHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.toolkits.base.Aggregator;
import soot.jimple.toolkits.scalar.DeadAssignmentEliminator;
import soot.jimple.toolkits.scalar.UnconditionalBranchFolder;
import soot.jimple.toolkits.scalar.UnreachableCodeEliminator;
import soot.options.Options;
import soot.toolkits.scalar.UnusedLocalEliminator;

public class CallGraphManager {
	private CallGraphManager(){}
	private static CallGraphManager thisOnly;
	private int MAXRETRYTIMES = 30;

	static public CallGraphManager v(){
		if(thisOnly == null){
			thisOnly = new CallGraphManager();
		}
		return thisOnly;
	}
	
	static public CallGraphManager reInit(){
		thisOnly = new CallGraphManager();
		return thisOnly;
	}
	
	private InfoflowConfiguration config = MTAScene.v().getInfoflowConfig();
	private IIPCManager ipcManager = MTAScene.v().getIPCManager();	
	private Collection<? extends PreAnalysisHandler> preProcessors = Collections.emptyList();	//����Ԥ����������չonBeforeCallgraphConstruction��onAfterCallgraphConstruction����ʵ�ִ���ǰ�ʹ����Ŀ���
	
	/**
	 * Constructs the callgraph
	 * @throws Exception 
	 */
	public void constructCallgraph() throws Exception {
		configCallGraphAlgorithm(null);
		
		// Some configuration options do not really make sense in combination
		if (config.getEnableStaticFieldTracking()
				&& InfoflowConfiguration.getAccessPathLength() == 0)
			throw new RuntimeException("Static field tracking must be disabled "
					+ "if the access path length is zero");
		if (InfoflowConfiguration.getAccessPathLength() < 0)
			throw new RuntimeException("The access path length may not be negative");
		// Clear the base registrations from previous runs
		AccessPathFactory.v().clearBaseRegister();
		
		// Allow the ICC manager to change the Soot Scene before we continue
		ipcManager.updateJimpleForICC();

		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onBeforeCallgraphConstruction();
        
//        // Patch the system libraries we need for callgraph construction��������"java.lang.Thread"��"android.os.Handler"	//!!!!!!Handler����ѽ��
//        MyMultiThreadPatcher mmtp = new MyMultiThreadPatcher();
//        mmtp.patchLibraries();
		
        // To cope with broken APK files, we convert all classes that are still
        // dangling after resolution into phantoms
        for (SootClass sc : Scene.v().getClasses())
        	if (sc.resolvingLevel() == SootClass.DANGLING) {
        		sc.setResolvingLevel(SootClass.BODIES);
        		sc.setPhantomClass();
        	}
        
		// We explicitly select the packs we want to run for performance
        // reasons. Do not re-run the callgraph algorithm if the host
        // application already provides us with a CG.
		if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand
				&& !Scene.v().hasCallGraph()) {
			int count = 0;
			while(true){
				if(applyPacks(count))
					break;
				count++;
			}
//			PackManager.v().getPack("wjpp").apply();
//	        PackManager.v().getPack("cg").apply();
		}
		
		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onAfterCallgraphConstruction();
	}

	private void resetG() throws Exception{
		G anotherG = new G();
		G global = G.v();
		for(Field f : G.class.getFields()){
			Object value = f.get(anotherG);
			try{f.set(global, value);}catch(Exception e){}
		}
		G.v().ClassHierarchy_classHierarchyMap.clear();
		G.v().MethodContext_map.clear();
	}

	private boolean applyPacks(int times) throws Exception {
		try{
			PackManager.v().getPack("wjpp").apply();
	        PackManager.v().getPack("cg").apply();
	        return true;
		}catch(UnresolvedClassException e){
			String msg = e.getMessage();
			if(!msg.startsWith("[KM-Unresolved] "))
				throw e;
			String toResolve = msg.replace("[KM-Unresolved] ", "");
			if(Options.v().debug_resolver())
				System.out.println(msg + ": " + Scene.v().getSootClass(toResolve.substring(1, toResolve.indexOf(":"))).isPhantom());
			Options.v().set_whole_program(false);
			
			SootMethod resolved = null;
			if(times < MAXRETRYTIMES)
				resolved = ClassResolveManager.v().extendResolving(toResolve, SootClass.SIGNATURES);
			else
				resolved = ClassResolveManager.v().extendResolving(toResolve, SootClass.BODIES);	//next time, it will not enter here.
			if(times > MAXRETRYTIMES + 1)
				throw new RuntimeException("Can not generate the call graph normally. Surpass the MAXRETRYTIMES limitation:" + times);
			for(InvokeExpr ie : e.mrList)
				ie.setMethodRef(resolved.makeRef());
			
			Options.v().set_whole_program(true);
			
			resetG();
			Scene.v().releaseFastHierarchy();
			Scene.v().releaseReachableMethods();
			Scene.v().releaseCallGraph();
			Scene.v().releaseSideEffectAnalysis();
			Scene.v().releasePointsToAnalysis();
			
			return false;
		}
	}

	static private void configCallGraphAlgorithm(String extraSeed) {
		// Configure the callgraph algorithm
		switch (MTAScene.v().getInfoflowConfig().getCallgraphAlgorithm()) {
			case AutomaticSelection:
				// If we analyze a distinct entry point which is not static,
				// SPARK fails due to the missing allocation site and we fall
				// back to CHA.
				if (extraSeed == null || extraSeed.isEmpty()) {
					Options.v().setPhaseOption("cg.spark", "on");
					Options.v().setPhaseOption("cg.spark", "string-constants:true");
				}
				else
					Options.v().setPhaseOption("cg.cha", "on");
				break;
			case CHA:
				Options.v().setPhaseOption("cg.cha", "on");
				break;
			case RTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "rta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case VTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "vta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case SPARK:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case OnDemand:
				// nothing to set here
				break;
			default:
				throw new RuntimeException("Invalid callgraph algorithm");
		}
		// Specify additional options required for the callgraph
		if (MTAScene.v().getInfoflowConfig().getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand) {
			Options.v().set_whole_program(true);
			Options.v().setPhaseOption("cg", "trim-clinit:false");
		}
	}

	public static void optimizeCG(Body body) {
//	    DeadAssignmentEliminator.v().transform(body);
//        UnreachableCodeEliminator.v().transform(body);
//        UnconditionalBranchFolder.v().transform(body);
////        Aggregator.v().transform(body);
//        UnusedLocalEliminator.v().transform(body);
	}
}
