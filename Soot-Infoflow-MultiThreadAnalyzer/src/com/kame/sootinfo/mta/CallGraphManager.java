package com.kame.sootinfo.mta;

import java.util.Collection;
import java.util.Collections;

import soot.Body;
import soot.Pack;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
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

	static public CallGraphManager v(){
		if(thisOnly == null){
			thisOnly = new CallGraphManager();
			configCallGraphAlgorithm(null);
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
	 */
	public void constructCallgraph(Body target) {
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
        // ����˵���е�DANGLING��Ҫת��ΪBODIES�����Phantom��
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
			PackManager.v().getPack("wjpp").apply();
	        if(target == null){
		        PackManager.v().getPack("cg").apply();
	        }
	        else{
		        PackManager.v().getPack("cg").apply(target);
	        }
		}
		
		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onAfterCallgraphConstruction();
	}

	public void constructCallgraph() {
		constructCallgraph(null);
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
