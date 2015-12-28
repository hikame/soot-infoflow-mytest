package com.kame.sootinfo.mta;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.myplugin.MyIPCManager;
import com.kame.sootinfo.mta.myplugin.MySSInterfacesSourceSinkManager;
import com.kame.sootinfo.mta.myplugin.MyTaintWrapper;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.INativeCallHandler;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.test.junit.MyMethodArgsSourceSinkManager;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;

public class MultiThreadAnalyzer {
//	private final Options opts = Options.v();
	
	public static String TargetSystemPath = "A:\\android-6.0.0_r1-MRA58K";
	public static String JavaLibPath = TargetSystemPath + "\\out\\target\\common\\obj\\JAVA_LIBRARIES";
	public static String AppPath = TargetSystemPath + "\\out\\target\\common\\obj\\APPS";

	private final Logger logger = LoggerFactory.getLogger(getClass());
	protected InfoflowConfiguration config = new InfoflowConfiguration();	
	protected List<String> targetMethodsList = new ArrayList<String>();
	protected List<String> sinksList = new ArrayList<String>();
	
	private ISourceSinkManager ssm = new MySSInterfacesSourceSinkManager(true, targetMethodsList, sinksList);		//1. 配置Source、Sink管理器
//	private ISourceSinkManager ssm = new MyMethodArgsSourceSinkManager(true, targetMethodsList, sinksList);
	private IIPCManager ipcManager = new MyIPCManager();			//2. 配置IPC管理器
	private ITaintPropagationWrapper taintWrapper = new MyTaintWrapper();
	private INativeCallHandler nativeCallHandler = new DefaultNativeCallHandler();  //5.  The NativeCallHandler defines the taint propagation behavior for native code

	//一些参数设置
	private final int accessPathLength = 5;	//InfoFlowConfig.accessPathLength
	private final boolean enableStaticFields = true; //InfoFlowConfig.enableStaticFields

	/**Config Classpath, EntryPoints & resolveClasses*/
	MyClassResolver myClassResolver = new MyClassResolver(constructClasspath(), targetMethodsList);
	/**Handle IPC, Multi-thread situation and generate CG*/
	MyCGConstructor myCGConstructor = new MyCGConstructor(config, ipcManager);
	/**Parser control flow */
	MyCFGParser myCFGPaerser = new MyCFGParser(config, ssm, taintWrapper);
	MyInfoFlowAnalyze myInfoFlowAnalyze = new MyInfoFlowAnalyze(config, ssm, taintWrapper, nativeCallHandler);
	MyHandlerHandler myHandlerHandler = new MyHandlerHandler();
	
	private void myTestConfig() throws Exception {
//		ssm = new MyMethodArgsSourceSinkManager(true, targetMethods, sinks);
		Options.v().set_verbose(true);
		Options.v().set_debug(true);
		Options.v().set_debug_resolver(true);
		Options.v().setPhaseOption("cg", "verbose:true");

		// The following config are important to achieve analysis in multi-threads.
		InfoflowConfiguration.setUseThisChainReduction(false);
		InfoflowConfiguration.setUseRecursiveAccessPaths(false);
//		config.setCodeEliminationMode(CodeEliminationMode.RemoveSideEffectFreeCode);
//		config.setEnableImplicitFlows(false);
		

//		targetMethodsList.add("<com.kame.mth.Main: void testThreadWithField0a(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThreadWithField0b(java.lang.String)>");
//		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandlerPost(java.lang.String)>");
		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandlerSendMSG(java.lang.String,java.lang.StringBuilder)>");
//		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandlerSendMSGAgain(java.lang.String)>");
//		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandlerSendMSGUnrelevant(java.lang.String)>");

		sinksList.add("<com.kame.mth.Publisher: void publish(java.lang.String)>");
		sinksList.add("<com.kame.tafhd.Publisher: void publish(java.lang.String)>");
	}
	
	private String constructClasspath() {		
		String cpSoot = "";
		try {
			cpSoot = appendLibOfClasspath();
		} catch (Exception e) {
			e.printStackTrace();
//			return null;
		}

		cpSoot = cpSoot + appendLibsFromPath(JavaLibPath);
cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestCodeForMultiThreadHandler\\bin";
cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestAPKForHandlerDevelopment\\bin\\classes";
System.out.println("ClassPath is: " + cpSoot);		
		return cpSoot.substring(1);
	}
	

	private void setIncludeList() {
		List<String> includeList = new LinkedList<String>();
		Options.v().set_include(includeList);
//		includeList.add("java.lang.*");
//		includeList.add("java.util.*");
//		includeList.add("java.io.*");
//		includeList.add("sun.misc.*");
//		includeList.add("java.net.*");
//		includeList.add("javax.servlet.*");
//		includeList.add("javax.crypto.*");

		includeList.add("android.*");
//		includeList.add("org.apache.http.*");

		includeList.add("de.test.*");
		includeList.add("soot.*");
		includeList.add("com.example.*");
		includeList.add("libcore.icu.*");
		includeList.add("securibench.*");
		includeList.add("com.kame.*");
	}

	private void setNonPhantomList() {
		List<String> npList = new LinkedList<String>();
		Options.v().setNonPhantomList(npList);
		npList.add("java.lang.*");
		npList.add("com.android.server.*");
		npList.add("android.os.Handler");
		npList.add("com.kame.*");
		npList.add("android.os.Message");
	}
	
	
	public static void main(String[] args) {
		try {
			new MultiThreadAnalyzer().begin();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void begin() throws Exception {
		initializeSoot();	
		myTestConfig();
		startAnalyze();
	}



	private void startAnalyze() throws Exception {		
		//Config classpath, entrypoints and resolve classes.
		myClassResolver.start();
		// Build the callgraph
		myCGConstructor.start();
		System.out.println("[TEST] " + Scene.v().getCallGraph());
		//cut down dead code & parse CFG
		myCFGPaerser.start();
		System.out.println("[TEST] " + Scene.v().getCallGraph());
		// do special handling for android.os.Handler
		if(myHandlerHandler.start(myCFGPaerser.getInfoflowCFG())){
			//重新构造
			ReachableMethods mths = Scene.v().getReachableMethods();
			CallGraph cg = Scene.v().getCallGraph();
			myCFGPaerser.start();
		}
System.out.println("[TEST] " + Scene.v().getCallGraph());
		//Information
		myInfoFlowAnalyze.start(myCFGPaerser.getInfoflowCFG());
	}

	private void initializeSoot() {
		// reset Soot:
		logger.info("Resetting Soot...");
		soot.G.reset();
		
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().setPhaseOption("jb", "use-original-names:true");
		
		configSootInfo();
		configCallGraphAlgorithm(null);	//我们的测试对象（SS interfaces）并不是类的main方法，如果是main方法，则此处需要给出具体方法描述的String

		setIncludeList();
		setNonPhantomList();
	}

	private void configCallGraphAlgorithm(String extraSeed) {
		// Configure the callgraph algorithm
		switch (config.getCallgraphAlgorithm()) {
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
		if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand) {
			Options.v().set_whole_program(true);
			Options.v().setPhaseOption("cg", "trim-clinit:false");
		}
		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		Options.v().set_src_prec(Options.src_prec_class);		//different from Original
	}

	private void configSootInfo() {			//......
		InfoflowConfiguration.setAccessPathLength(accessPathLength);
		config.setEnableStaticFieldTracking(enableStaticFields);
		config.setIgnoreFlowsInSystemPackages(false);	//...
	}
	
	private String appendLibsFromPath(String path) {
		String result = "";
		File outFolder = new File(path);
		if(outFolder == null || !outFolder.exists() || !outFolder.isDirectory())
			return "";
		for(File intermediates : outFolder.listFiles()){
			if(intermediates == null || !intermediates.exists() || !intermediates.isDirectory())
				continue;
			
			File clssFolder = new File(intermediates.getAbsolutePath() + File.separator + "classes");
			if(clssFolder.exists() && clssFolder.isDirectory()){
				result = result + File.pathSeparator + clssFolder.getAbsolutePath();
				continue;
			}
			File dex2jar = new File(intermediates.getAbsolutePath() + File.separator + "classes-dex2jar.jar");
			if(dex2jar.exists()){
				result = result + File.pathSeparator + dex2jar.getAbsolutePath();
				continue;
			}
			File jar = new File(intermediates.getAbsolutePath() + File.separator + "classes.jar");
			if(jar.exists()){
				result = result + File.pathSeparator + jar.getAbsolutePath();
				continue;
			}
		}
		return result;
	}

	private String appendLibOfClasspath() throws Exception {
		String result = "";
		File file = new File(TargetSystemPath + File.separator + ".classpath");
		BufferedReader br = new BufferedReader(new FileReader(file));
		String line = null;
		while((line = br.readLine()) != null){
			if(!line.contains("<classpathentry kind=\"lib\""))
				continue;
			String mark = "path=\"";
			line = TargetSystemPath + File.separator + line.substring(line.indexOf(mark) + mark.length()).replace("\"/>", "");
//			apclsList.add(line.replace("/", File.separator).replace("\\", )File.separator));
			result = result 
					+ File.pathSeparator 
					+ line.replace("/", File.separator).replace("\\", File.separator);
		}
		br.close();
		return result;
	}
}
