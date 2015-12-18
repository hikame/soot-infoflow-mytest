package com.kame.sootinfo.mta;

import java.util.Collection;
import java.util.Collections;

import com.kame.sootinfo.mta.myplugin.MyMultiThreadPatcher;

import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.cfg.LibraryClassPatcher;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.handlers.PreAnalysisHandler;
import soot.jimple.infoflow.ipc.IIPCManager;

public class MyCGConstructor {
	private InfoflowConfiguration config;
	private IIPCManager ipcManager;
	private Collection<? extends PreAnalysisHandler> preProcessors = Collections.emptyList();	//配置预处理器，扩展onBeforeCallgraphConstruction和onAfterCallgraphConstruction方法实现处理前和处理后的控制
	
	public MyCGConstructor(InfoflowConfiguration cf, IIPCManager ipcm){
		config = cf;
		ipcManager = ipcm;
	}
	
	public void start(){
		constructCallgraph();
	}
	
	/**
	 * Constructs the callgraph
	 */
	protected void constructCallgraph() {
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
        
//        // Patch the system libraries we need for callgraph construction，包括了"java.lang.Thread"和"android.os.Handler"	//!!!!!!Handler机制呀！
//        MyMultiThreadPatcher mmtp = new MyMultiThreadPatcher();
//        mmtp.patchLibraries();
		
        // To cope with broken APK files, we convert all classes that are still
        // dangling after resolution into phantoms
        // 所以说所有的DANGLING都要转换为BODIES级别的Phantom类
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
	        PackManager.v().getPack("cg").apply();
		}
		
		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onAfterCallgraphConstruction();
	}
}
