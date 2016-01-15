package com.kame.sootinfo.mta;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.options.Options;

public class MainClass {
	private static int MAX_CFG_GENERATE_TIMES = 5;
	public static String TargetSystemPath = "E:\\android-6.0.0_r1-MRA58K";
	public static String JavaLibPath = TargetSystemPath + "\\out\\target\\common\\obj\\JAVA_LIBRARIES";
	public static String AppPath = TargetSystemPath + "\\out\\target\\common\\obj\\APPS";
	private final Logger logger = LoggerFactory.getLogger(getClass());
	String sourceSinkFile = "EasyTaintWrapperSource.txt";

	//一些参数设置
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
		//我们的测试对象（SS interfaces）并不是类的main方法，如果是main方法，则此处需要给出具体方法描述的String
		configCallGraphAlgorithm(null);	
		testConfig();
		constructClasspath();
		ClassResolveManager.v().start();
		AndroidHandlerProcessor.v().handleDispatchMsg();
		InfoflowAnalyzer.v().start();
	}


//
//	private void startAnalyze() throws Exception {		
//		//Config classpath, entrypoints and resolve classes.
//		ClassResolveManager.v().start();
//		List<String> unResolvedMethods;
//		int count = 0;
//		do{
//			//cut down dead code & parse CFG
//			ControlFlowGraphManager.v().start();
//			unResolvedMethods = findUnresolved(ClassResolveManager.v().getInvokedMethods(), 
//					ControlFlowGraphManager.v().getInfoflowCFG());
//			ClassResolveManager.v().doResolve(unResolvedMethods);
//			count++;
//		}while(unResolvedMethods.size() > 0 || count > MAX_CFG_GENERATE_TIMES);
//		// do special handling for android.os.Handler
//		if(AndroidHandlerProcessor.v().start()){
//			//重新构造
//			ControlFlowGraphManager.v().start();
//		}
//		InfoflowAnalyzer.v().start();
//	}

//	private List<String> findUnresolved(List<String> invokedMths, IInfoflowCFG cfg) {
//		List<String> result = new ArrayList<String>();
//		for(String mthSig : invokedMths){	//其中包含了一些phantom的类~
//			SootMethod sm = Scene.v().getMethod(mthSig);
//			if(sm.isPhantom()){
//				Set<Unit> callUnitSet = cfg.getCallsFromWithin(sm);
//				for(Unit cu : callUnitSet){
//					Collection<SootMethod> calledMths = cfg.getCalleesOfCallAt(cu);
//					for(SootMethod mt : calledMths){
//						String sig = mt.getSignature();
//						if(!invokedMths.contains(sig))
//							result.add(sig);
//					}
//				}
//			}
//		}
//		return result;
//	}

	private void initializeSoot() {
		// reset Soot:
		logger.info("Resetting Soot...");
		soot.G.reset();
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().setPhaseOption("jb", "use-original-names:true");
	}
	

	private void configCallGraphAlgorithm(String extraSeed) {
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
		
		MTAScene.v().getInfoflowConfig().setInspectSinks(true);
		
		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		Options.v().set_src_prec(Options.src_prec_class);		//different from Original
	}

	private void configSootInfoflow() {
		InfoflowConfiguration.setAccessPathLength(accessPathLength);
		MTAScene.v().getInfoflowConfig().setEnableStaticFieldTracking(enableStaticFields);
		MTAScene.v().getInfoflowConfig().setIgnoreFlowsInSystemPackages(false);
		MTAScene.v().getInfoflowConfig().setWriteOutputFiles(true);
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
