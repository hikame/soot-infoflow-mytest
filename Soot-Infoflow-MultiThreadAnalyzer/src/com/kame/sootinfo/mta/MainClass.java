package com.kame.sootinfo.mta;

import java.io.File;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import com.kame.sootinfo.mta.myplugin.MySourceSinkManager;

import soot.G;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.options.Options;

public class MainClass {
	public static String TargetSystemPath = "E:\\android-5.1.0_r3-LMY47I";
	public static String JavaLibPath = TargetSystemPath + "\\out\\target\\common\\obj\\JAVA_LIBRARIES";
	public static String AppPath = TargetSystemPath + "\\out\\target\\common\\obj\\APPS";
	private final Logger logger = LoggerFactory.getLogger(getClass());
	String sourceSinkFile = "EasyTaintWrapperSource.txt";
	String classPath = null;

	private final int accessPathLength = 5;	//InfoFlowConfig.accessPathLength
	private final boolean enableStaticFields = true; //InfoFlowConfig.enableStaticFields
	
	Map<String, List<String>> ssInterfaceMap = new HashMap<String, List<String>>();
	private void testConfig(String signature) throws Exception {
//		Options.v().set_verbose(true);
//		Options.v().set_debug(true);
//		Options.v().set_debug_resolver(true);
//		Options.v().setPhaseOption("cg", "verbose:true");
		
		// The following config are important to achieve analysis in multi-threads.
		String resultPath = "ResultFolder";
		File resultFolder = new File(resultPath);
		if(!resultFolder.exists())
			resultFolder.mkdirs();
		MTAScene.v().setResultFolder(resultFolder);
		
		InfoflowConfiguration.setUseThisChainReduction(false);
		InfoflowConfiguration.setUseRecursiveAccessPaths(false);
		
		MTAScene.v().setSourceSinkFile(sourceSinkFile);
		MTAScene.v().enableNatureSource(false);	//nature source not allowed. such as obj = null.
		MTAScene.v().getInfoflowConfig().setCodeEliminationMode(CodeEliminationMode.RemoveSideEffectFreeCode);

		List<String> targetMethodsList = new ArrayList<String>();
		MTAScene.v().setTargetList(targetMethodsList);
		List<String> sinksList = new ArrayList<String>();
		MTAScene.v().setSinkMethodList(sinksList);

		targetMethodsList.add(signature);
//		targetMethodsList.add("<com.android.server.pm.PackageManagerService: android.content.pm.PackageCleanItem nextPackageToClean(android.content.pm.PackageCleanItem)>");
//		targetMethodsList.add("<com.android.server.ConnectivityService: void releasePendingNetworkRequest(android.app.PendingIntent)>");
//		sinksList.add("<com.kame.tafhd.Publisher: void publish(java.lang.String)>");
	}
	
	private void constructClasspath() {		
		if(classPath == null){
			String cpSoot = "";
			cpSoot = cpSoot + appendLibsFromPath(JavaLibPath);
			cpSoot = cpSoot + appendLibsFromPath(AppPath);
			cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestCodeForMultiThreadHandler\\bin";
			cpSoot = cpSoot + File.pathSeparator + "E:\\GitHub_Projects\\soot-infoflow-mytest\\TestAPKForHandlerDevelopment\\bin\\classes";
			cpSoot = cpSoot.substring(1);
			classPath = cpSoot;
		}
		Options.v().set_soot_classpath(classPath);
	}

	
	public static void main(String[] args) {
		try {
			new MainClass().begin();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void begin() throws Exception {
		Class.forName("org.sqlite.JDBC");
		configSootInfoflow();
		String dbUrl = "jdbc:sqlite:SSInterfaces.db";
		Connection dbConn =DriverManager.getConnection(dbUrl);
		Statement stat = dbConn.createStatement();
		MTAScene.v().setDBStatement(stat);
		ResultSet results = stat.executeQuery("select name from System_Service_Information where noInterface is null");
		while(results.next()){
			String sername = results.getString(1).replace(".", "__");
			ssInterfaceMap.put(sername, new ArrayList<String>());
		}
		results.close();
		
		for(String serviceName : ssInterfaceMap.keySet()){
			String sql = String.format("select signature from %s where result is null and analyzeError is null", serviceName);
			results = stat.executeQuery(sql);
			while(results.next()){
				String signature = results.getString(1);
				ssInterfaceMap.get(serviceName).add(signature);
			}
			results.close();
		}
		
		int count = 0;
		for(String serviceName : ssInterfaceMap.keySet()){
//if(serviceName.equals("appwidget"))
//	continue;
//if(serviceName.equals("content"))
//	continue;
//Scene.v().getClasses().size();
			logger.info("Start analyzing service: " + serviceName);
			MTAScene.v().setCurrentService(serviceName);
			for(String sig : ssInterfaceMap.get(serviceName)){
				logger.info(String.format("-> [%d] Start analyzing interface(%s): %s", count, serviceName.replace("__", "."), sig));
				try{
if(sig.toString().equals("<com.android.server.am.ActivityManagerService: boolean bindBackupAgent(android.content.pm.ApplicationInfo,int)>"))
	continue;
					analyzeInterface(sig);
				}catch(Exception e){
					e.printStackTrace();
					String cmd = String.format(
							"update %s set analyzeError = \"%s\" where signature = \"%s\"", 
							serviceName, e.getClass().getName() + e.getMessage(), sig);
//							serviceName, e.toString().replace("\'", "").replace("\"", ""), sig);
					stat.executeUpdate(cmd);
				}
				count++;
			}
		}
		stat.close();
		dbConn.close();
	}

	

	private void analyzeInterface(String signature) throws Exception {
signature = "<com.android.server.ConnectivityService: void releasePendingNetworkRequest(android.app.PendingIntent)>";
MTAScene.v().setCurrentService("connectivity");
logger.info("[FOR TEST] Change the test target to: " + signature);
		MTAScene.v().setStartTime(System.currentTimeMillis());
		G.reset();
		initializeSoot();
		testConfig(signature);
		ClassResolveManager.reInit();
		CallGraphManager.reInit();
		ControlFlowGraphManager.reInit();
		
		
		logger.info("Config the class path.");
		constructClasspath();
		
		logger.info("Start resolve the classes.");
		ClassResolveManager.v().start();
		CallGraphManager.reInit().constructCallgraph();
		ControlFlowGraphManager.v().generateCFG();
		logger.info("Handling the dispatchMessage() method invocations.");
		AndroidHandlerProcessor.reInit().run();
//SootMethod sm = Scene.v().getMethod("<com.android.server.am.ActivityManagerService$2: void handleMethod(android.os.Message)>");
		logger.info("Reconstruct the control flow graph for the infoflow analyzer.");
		ControlFlowGraphManager.v().eliminateDeadCode(new MySourceSinkManager());
		ControlFlowGraphManager.v().generateCFG(); //in order to take care of infoflow analysis.
		
		String cmd = String.format("update %s set callgraphSize = %d, classSize = %d, phantomeClassSize = %d, reachableMethodSize = %d where signature = \"%s\"", 
				MTAScene.v().getCurrentService(),
				Scene.v().getCallGraph().size(),
				Scene.v().getClasses().size(),
				Scene.v().getPhantomClasses().size(),
				Scene.v().getReachableMethods().size(),
				signature);
		MTAScene.v().getDBStatement().execute(cmd);
		
		logger.info("Start the infoflow analysis.");
		InfoflowAnalyzer.reInit().start();
		
//		logger.info("Output the transformed Jimple files.");
//		if (MTAScene.v().getInfoflowConfig().getWriteOutputFiles())
//			try{
//				PackManager.v().writeOutput();
//			}catch(Exception e){
//				e.printStackTrace();
//			}
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
