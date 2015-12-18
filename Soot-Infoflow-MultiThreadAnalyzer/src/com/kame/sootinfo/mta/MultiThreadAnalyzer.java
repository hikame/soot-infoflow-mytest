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
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.INativeCallHandler;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.test.junit.MyMethodArgsSourceSinkManager;
import soot.options.Options;

public class MultiThreadAnalyzer {
//	private final Options opts = Options.v();
	
	public static String TargetSystemPath = "A:\\android-6.0.0_r1-MRA58K";
	public static String JavaLibPath = TargetSystemPath + "\\out\\target\\common_bak\\obj\\JAVA_LIBRARIES";
	public static String AppPath = TargetSystemPath + "\\out\\target\\common_bak\\obj\\APPS";
	private static String JarsFolderPath = "A:\\workspace\\JarsForSootOnAndroid";

	private final Logger logger = LoggerFactory.getLogger(getClass());
	protected InfoflowConfiguration config = new InfoflowConfiguration();	
	protected List<String> targetMethodsList = new ArrayList<String>();
	protected List<String> sinksList = new ArrayList<String>();
	
	private ISourceSinkManager ssm = new MySSInterfacesSourceSinkManager(true, targetMethodsList, sinksList);		//1. ����Source��Sink������
//	private ISourceSinkManager ssm = new MyMethodArgsSourceSinkManager(true, targetMethodsList, sinksList);
	private IIPCManager ipcManager = new MyIPCManager();			//2. ����IPC������
	private ITaintPropagationWrapper taintWrapper = new MyTaintWrapper();
	private INativeCallHandler nativeCallHandler = new DefaultNativeCallHandler();  //5.  The NativeCallHandler defines the taint propagation behavior for native code

	//һЩ��������
	private final int accessPathLength = 5;	//InfoFlowConfig.accessPathLength
	private final boolean enableStaticFields = true; //InfoFlowConfig.enableStaticFields

	/**Config Classpath, EntryPoints & resolveClasses*/
	MyClassResolver myClassResolver = new MyClassResolver(constructClasspath(), targetMethodsList);
	/**Handle IPC, Multi-thread situation and generate CG*/
	MyCGConstructor myCGConstructor = new MyCGConstructor(config, ipcManager);
	/**Parser control flow */
	MyCFGParser myCFGPaerser = new MyCFGParser(config, ssm, taintWrapper);
	MyInfoFlowAnalyze myInfoFlowAnalyze = new MyInfoFlowAnalyze(config, ssm, taintWrapper, nativeCallHandler);
	
	private void myTestConfig() throws Exception {
//		ssm = new MyMethodArgsSourceSinkManager(true, targetMethods, sinks);
		Options.v().set_verbose(true);
		Options.v().set_debug(true);
		Options.v().set_debug_resolver(true);
		Options.v().setPhaseOption("cg", "verbose:true");

//		targetMethodsList.add("<com.kame.mth.Main: void testThread0(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThread1(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThread2(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThread3(java.lang.String)>");

//		targetMethodsList.add("<com.kame.tafhd.MainActivity: void testHandler(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThreadWithField0a(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThreadWithField0b(java.lang.String)>");
//		targetMethodsList.add("<com.kame.mth.Main: void testThreadWithField1(java.lang.String)>");
		
		targetMethodsList.add("<com.kame.mth.Main: void simpleTest(java.lang.String)>");
		
		sinksList.add("<com.kame.mth.Publisher: void publish(java.lang.String)>");
		sinksList.add("<com.kame.tafhd.Publisher: void publish(java.lang.String)>");
		
//		targetMethodsList.add("<com.android.server.pm.PackageManagerService: " +
//				"void movePackageInternal(" +
//				"java.lang.String,java.lang.String,int)>");
		
//		sinksList.add("<android.os.Handler: boolean sendMessage(android.os.Message)>");
//		sinksList.add("<java.lang.Thread: void start()>");
//		sinksList.add("<com.android.server.pm.PackageManagerService$MoveCallbacks: void notifyStatusChanged(int,int)>");
	}
	
	private String constructClasspath() {		
		String cpSoot;
		try {
			cpSoot = appendLibOfClasspath();
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
		cpSoot = cpSoot + appendLibsFromPath(JavaLibPath);
cpSoot = cpSoot + File.pathSeparator + "E:\\Android\\Soot\\soot-infoflow-mytest\\TestCodeForMultiThreadHandler\\bin";
cpSoot = cpSoot + File.pathSeparator + "E:\\Android\\Soot\\soot-infoflow-mytest\\TestAPKForHandlerDevelopment\\bin\\classes";
		
		return cpSoot.substring(1);
	}
	

	private void setIncludeList() {
		List<String> includeList = new LinkedList<String>();
		Options.v().set_include(includeList);
		includeList.add("java.lang.*");
		includeList.add("java.util.*");
		includeList.add("java.io.*");
		includeList.add("sun.misc.*");
		includeList.add("java.net.*");
		includeList.add("javax.servlet.*");
		includeList.add("javax.crypto.*");

		includeList.add("android.*");
		includeList.add("org.apache.http.*");

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



	private void startAnalyze() {		
		//Config classpath, entrypoints and resolve classes.
		myClassResolver.start();
		// Build the callgraph
		myCGConstructor.start();
		//cut down dead code & parse CFG
		myCFGPaerser.start();
		
		myInfoFlowAnalyze.setInfoflowCFG(myCFGPaerser.getInfoflowCFG());
		
		//Information Flow Analyze
		myInfoFlowAnalyze.start();
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
		configCallGraphAlgorithm(null);	//���ǵĲ��Զ���SS interfaces�����������main�����������main��������˴���Ҫ�������巽��������String

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