package com.kame.sootinfo.mta;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Scene;
import soot.SootClass;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.options.Options;

public class MyClassResolver {

	private final Logger logger = LoggerFactory.getLogger(getClass());
	private String classpath; 
	private List<String> entryPoints = new ArrayList<String>();
	
	public MyClassResolver(String cp, List<String> eps){
		classpath = cp;
		entryPoints = eps;
	}

	public void start(){
		Options.v().set_soot_classpath(classpath);
// Patch the system libraries we need for callgraph construction，包括了"java.lang.Thread"和"android.os.Handler"	//!!!!!!Handler机制呀！
		new MyMultiThreadPatcher().patchLibraries();
		resolveClasses(setDummyEntryPoints());
	}

	private IEntryPointCreator setDummyEntryPoints() {
		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		IEntryPointCreator epc = new DefaultEntryPointCreator(entryPoints);
		Scene.v().setEntryPoints(Collections.singletonList(epc.createDummyMain()));
		return epc;
	}

	private void resolveClasses(IEntryPointCreator epc) {
      
		Collection<String> classes = epc.getRequiredClasses();
		for (String className : classes)
			Scene.v().addBasicClass(className, SootClass.BODIES);
		Scene.v().loadNecessaryClasses();
		logger.info("Basic class loading done.");
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			if (c != null)
				c.setApplicationClass();
		}
	}
}
