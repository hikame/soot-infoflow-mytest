package com.kame.sootinfo.mta;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.myplugin.MySourceSinkManager;

import soot.Body;
import soot.FastHierarchy;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;

public class MainClass {
	public static String TargetSystemPath = "E:\\android-6.0.0_r1-MRA58K";
	public static String JavaLibPath = TargetSystemPath + "\\out\\target\\common\\obj\\JAVA_LIBRARIES";
	public static String AppPath = TargetSystemPath + "\\out\\target\\common\\obj\\APPS";
	private final Logger logger = LoggerFactory.getLogger(getClass());
	String sourceSinkFile = "EasyTaintWrapperSource.txt";

	private final int accessPathLength = 5;	//InfoFlowConfig.accessPathLength
	private final boolean enableStaticFields = true; //InfoFlowConfig.enableStaticFields
	
	private void testConfig() throws Exception {
		Options.v().set_verbose(true);
		Options.v().set_debug(true);
		Options.v().set_debug_resolver(true);
		Options.v().setPhaseOption("cg", "verbose:true");

		// The following config are important to achieve analysis in multi-threads.
		InfoflowConfiguration.setUseThisChainReduction(false);
		InfoflowConfiguration.setUseRecursiveAccessPaths(false);
		
		MTAScene.v().setSourceSinkFile(sourceSinkFile);
		
		MTAScene.v().getInfoflowConfig().setCodeEliminationMode(CodeEliminationMode.RemoveSideEffectFreeCode);
//		config.setEnableImplicitFlows(true);

		List<String> targetMethodsList = new ArrayList<String>();
		MTAScene.v().setTargetList(targetMethodsList);
		List<String> sinksList = new ArrayList<String>();
		MTAScene.v().setSinkMethodList(sinksList);
		
		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandlerSendMSG(java.lang.String)>");
//		targetMethodsList.add("<com.android.server.pm.PackageManagerService: android.content.pm.PackageCleanItem nextPackageToClean(android.content.pm.PackageCleanItem)>");
		sinksList.add("<com.kame.tafhd.Publisher: void publish(java.lang.String)>");
	}
	
	private String constructClasspath() {		
		String cpSoot = "";

		cpSoot = cpSoot + appendLibsFromPath(JavaLibPath);
cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestCodeForMultiThreadHandler\\bin";
cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestAPKForHandlerDevelopment\\bin\\classes";
		cpSoot = cpSoot.substring(1);
		Options.v().set_soot_classpath(cpSoot);
		return cpSoot;
	}

	
	public static void main(String[] args) {
		try {
			new MainClass().begin();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void begin() throws Exception {
		initializeSoot();
		
		configSootInfoflow();
		testConfig();
		
		logger.info("Start constuct the class path.");
		constructClasspath();
		
		logger.info("Start resolve the classes.");
		ClassResolveManager.v().start();

		ControlFlowGraphManager.v().generateCFG();
		logger.info("Handling the dispatchMessage() method invocations.");
		AndroidHandlerProcessor.v().handleDispatchMsg();
		
//test();	

		logger.info("Reconstruct the control flow graph for the infoflow analyzer.");
//		ControlFlowGraphManager.v().eliminateDeadCode(new MySourceSinkManager());
		ControlFlowGraphManager.v().generateCFG(); //in order to take care of infoflow analysis.

//		Scene.v().releaseFastHierarchy();
//		FastHierarchy fh = Scene.v().getOrMakeFastHierarchy();
		logger.info("Start the infoflow analysis.");
		InfoflowAnalyzer.v().start();
		
		logger.info("Output the transformed Jimple files.");
		if (MTAScene.v().getInfoflowConfig().getWriteOutputFiles())
			PackManager.v().writeOutput();
	}

	private void test() {
		SootMethod msgobtain = Scene.v().getMethod("<android.os.Handler: boolean sendEmptyMessage(int)>");
		IInfoflowCFG cfg = ControlFlowGraphManager.v().getInfoflowCFG();
		Collection<Unit> mbCallers = cfg.getCallersOf(msgobtain);
		
		for(Unit caller : mbCallers){
			SootMethod sm = null;
			try{sm = cfg.getMethodOf(caller);}catch(Exception e){
				System.out.println("[ER] " + caller);
				continue;
			};
			System.out.println("[MB]" + sm.toString());
			Body body = sm.getActiveBody();
//			System.out.println(sm.getActiveBody().toString());
			SootClass sc = sm.getDeclaringClass();
			sc.toString();
		}
		
		System.out.println(msgobtain.getActiveBody().toString());
		return;
//		Scene.v().releaseFastHierarchy();
//		FastHierarchy fh = Scene.v().getOrMakeFastHierarchy();
//		SootClass pms1 = Scene.v().getSootClass("com.android.server.pm.PackageManagerService$1");
//		SootClass sel = Scene.v().getSootClass("android.os.storage.StorageEventListener");
//		Collection<SootClass> subclasses = fh.getSubclassesOf(sel);
//		boolean tmp1 = fh.canStoreType(sel.getType(), pms1.getType());
//		boolean tmp2 = fh.canStoreType(pms1.getType(), sel.getType());;
//		return;
	}

	private void initializeSoot() {
		// reset Soot:
		logger.info("Resetting Soot...");
		soot.G.reset();
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().setPhaseOption("jb.ulp", "off");
		Options.v().set_src_prec(Options.src_prec_jimple);		//different from Original
//		Options.v().set_src_prec(Options.src_prec_class);		//different from Original
	}

	private void configSootInfoflow() {
		InfoflowConfiguration.setAccessPathLength(accessPathLength);
		MTAScene.v().getInfoflowConfig().setEnableStaticFieldTracking(enableStaticFields);
		MTAScene.v().getInfoflowConfig().setIgnoreFlowsInSystemPackages(false);
		MTAScene.v().getInfoflowConfig().setWriteOutputFiles(true);
		MTAScene.v().getInfoflowConfig().setInspectSinks(true);
		
//		MTAScene.v().getInfoflowConfig().setCallgraphAlgorithm(CallgraphAlgorithm.VTA);
//		MTAScene.v().getInfoflowConfig().setCallgraphAlgorithm(CallgraphAlgorithm.CHA);
	}
	
	private String appendLibsFromPath(String path) {
		String result = "";
		File outFolder = new File(path);
		if(outFolder == null || !outFolder.exists() || !outFolder.isDirectory())
			return "";
		for(File intermediates : outFolder.listFiles()){
			if(intermediates == null || !intermediates.exists() || !intermediates.isDirectory())
				continue;
			
			String absolutePath = intermediates.getAbsolutePath();
			if(absolutePath.contains("android_stubs_current_intermediates") ||
					absolutePath.contains("sdk_v"))
				continue;
			
			File clssFolder = new File(absolutePath + File.separator + "classes");
			if(clssFolder.exists() && clssFolder.isDirectory()){
				result = result + File.pathSeparator + clssFolder.getAbsolutePath();
				continue;
			}
			
			File dex2jar = new File(absolutePath + File.separator + "classes-dex2jar.jar");
			if(dex2jar.exists()){
				result = result + File.pathSeparator + dex2jar.getAbsolutePath();
				continue;
			}

			File jar = new File(absolutePath + File.separator + "classes.jar");
			if(jar.exists()){
				result = result + File.pathSeparator + jar.getAbsolutePath();
				continue;
			}
		}
		return result;
	}
//
//	private String appendLibOfClasspath() throws Exception {
//		String result = "";
//		File file = new File(TargetSystemPath + File.separator + ".classpath");
//		BufferedReader br = new BufferedReader(new FileReader(file));
//		String line = null;
//		while((line = br.readLine()) != null){
//			if(!line.contains("<classpathentry kind=\"lib\""))
//				continue;
//			String mark = "path=\"";
//			line = TargetSystemPath + File.separator + line.substring(line.indexOf(mark) + mark.length()).replace("\"/>", "");
////			apclsList.add(line.replace("/", File.separator).replace("\\", )File.separator));
//			result = result 
//					+ File.pathSeparator 
//					+ line.replace("/", File.separator).replace("\\", File.separator);
//		}
//		br.close();
//		return result;
//	}
}
