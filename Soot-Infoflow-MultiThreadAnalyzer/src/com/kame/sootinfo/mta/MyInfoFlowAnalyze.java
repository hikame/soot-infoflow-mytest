package com.kame.sootinfo.mta;

import heros.solver.CountingThreadPoolExecutor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kame.sootinfo.mta.myplugin.MySourceSinkManager;
import com.kame.sootinfo.mta.myplugin.MyTaintPropagationHandler;
import com.kame.sootinfo.mta.tags.MyMethodTag;
import com.kame.sootinfo.mta.tags.MyStmtTag;

import soot.IdentityUnit;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.aliasing.FlowSensitiveAliasStrategy;
import soot.jimple.infoflow.aliasing.IAliasingStrategy;
import soot.jimple.infoflow.aliasing.PtsBasedAliasStrategy;
import soot.jimple.infoflow.cfg.BiDirICFGFactory;
import soot.jimple.infoflow.cfg.DefaultBiDiICFGFactory;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AbstractionAtSink;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.FlowDroidMemoryManager;
import soot.jimple.infoflow.data.SourceContextAndPath;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory;
import soot.jimple.infoflow.data.pathBuilders.IAbstractionPathBuilder;
import soot.jimple.infoflow.data.pathBuilders.IPathBuilderFactory;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory.PathBuilder;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.nativ.INativeCallHandler;
import soot.jimple.infoflow.problems.BackwardsInfoflowProblem;
import soot.jimple.infoflow.problems.InfoflowProblem;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.solver.IMemoryManager;
import soot.jimple.infoflow.solver.cfg.BackwardsInfoflowCFG;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.solver.fastSolver.InfoflowSolver;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JimpleLocalBox;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.kame.SourceSinkType;
import soot.options.Options;
import soot.tagkit.StringTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph.ExceptionDest;
import soot.util.Chain;
import soot.util.MultiMap;

public class MyInfoFlowAnalyze {

	private final Logger logger = LoggerFactory.getLogger(getClass());
	private final InfoflowConfiguration config;
	private final ISourceSinkManager ssm;
	private final ITaintPropagationWrapper taintWrapper;
	private INativeCallHandler nativeCallHandler;
	private IInfoflowCFG iCfg;
	
	IAliasingStrategy aliasingStrategy = null;
	Aliasing aliasing = null;
	protected IPathBuilderFactory pathBuilderFactory = new DefaultPathBuilderFactory(PathBuilder.ContextSensitive, true);
//	protected IPathBuilderFactory pathBuilderFactory = new DefaultPathBuilderFactory();
	private MyTaintPropagationHandler taintPropagationHandler;		//4.a Handler interface for callbacks during taint propagation�����Բ�������
	private TaintPropagationHandler backwardsPropagationHandler = null;  //4.b Handler interface for callbacks during taint propagation�����Բ�������
	private Set<ResultsAvailableHandler> onResultsAvailable = new HashSet<ResultsAvailableHandler>();
	
    private long maxMemoryConsumption = -1;
	private InfoflowResults results = null;
	
	public MyInfoFlowAnalyze(InfoflowConfiguration cf, ISourceSinkManager is, ITaintPropagationWrapper tw, INativeCallHandler nch){
			config = cf;
			ssm = is;
			taintWrapper = tw;
			nativeCallHandler = nch;
			//TODO ʵ�������Լ���propagation��ʵ�ֶ���MyStmtTag�еĸ���value�Ŀ���source���͵Ĵ��ݣ����������ݼ��ʱ�Ĵ���
			taintPropagationHandler = new MyTaintPropagationHandler();
	}
	
	private enum StmtThreadType{
		StartMultiThread,
		ReturnMultiThread,
		None
	}
	
	public void start(IInfoflowCFG iInfoflowCFG) {
		iCfg = iInfoflowCFG;
        int numThreads = Runtime.getRuntime().availableProcessors();
		CountingThreadPoolExecutor executor = createExecutor(numThreads);
		// Initialize the memory manager
		IMemoryManager<Abstraction> memoryManager = new FlowDroidMemoryManager();
		
		// Initialize the data flow manager
		InfoflowManager manager = new InfoflowManager(config, null, iCfg, ssm, taintWrapper);
		
		BackwardsInfoflowProblem backProblem = null;
		InfoflowManager backwardsManager = null;
		InfoflowSolver backSolver = null;
		switch (config.getAliasingAlgorithm()) {
			case FlowSensitive:
				backwardsManager = new InfoflowManager(config, null,
						new BackwardsInfoflowCFG(iCfg), ssm, taintWrapper);
				backProblem = new BackwardsInfoflowProblem(backwardsManager);
				backSolver = new InfoflowSolver(backProblem, executor);
				backSolver.setMemoryManager(memoryManager);
				backSolver.setJumpPredecessors(!pathBuilderFactory.supportsPathReconstruction());				
				aliasingStrategy = new FlowSensitiveAliasStrategy(iCfg, backSolver);
				break;
			case PtsBased:
				backProblem = null;
				backSolver = null;
				aliasingStrategy = new PtsBasedAliasStrategy(iCfg);
				break;
			default:
				throw new RuntimeException("Unsupported aliasing algorithm");
		}
		
		// Get the zero fact��������ֵ�����۵�����Ϊ�յ�ʱ�򣬼�Ϊ��ֵ��
		Abstraction zeroValue = backProblem != null ? backProblem.createZeroValue() : null;
		InfoflowProblem forwardProblem  = new InfoflowProblem(manager,
				aliasingStrategy, zeroValue);
		
		taintPropagationHandler.generateAliasing(aliasingStrategy, iCfg);
		taintPropagationHandler.setMemoryManager(memoryManager);
		// Set the options
		InfoflowSolver forwardSolver = new InfoflowSolver(forwardProblem, executor);
		aliasingStrategy.setForwardSolver(forwardSolver);
		manager.setForwardSolver(forwardSolver);
		if (backwardsManager != null)
			backwardsManager.setForwardSolver(forwardSolver);
		
		forwardSolver.setMemoryManager(memoryManager);
		forwardSolver.setJumpPredecessors(!pathBuilderFactory.supportsPathReconstruction());
//		forwardSolver.setEnableMergePointChecking(true);
		
		forwardProblem.setTaintPropagationHandler(taintPropagationHandler);
		forwardProblem.setTaintWrapper(taintWrapper);
		if (nativeCallHandler != null)
			forwardProblem.setNativeCallHandler(nativeCallHandler);
		
		if (backProblem != null) {
			backProblem.setForwardSolver(forwardSolver);
			backProblem.setTaintPropagationHandler(backwardsPropagationHandler);
			backProblem.setTaintWrapper(taintWrapper);
			if (nativeCallHandler != null)
				backProblem.setNativeCallHandler(nativeCallHandler);
			backProblem.setActivationUnitsToCallSites(forwardProblem);
		}
		
		// Print our configuration
		config.printSummary();
		if (config.getFlowSensitiveAliasing() && !aliasingStrategy.isFlowSensitive())
			logger.warn("Trying to use a flow-sensitive aliasing with an "
					+ "aliasing strategy that does not support this feature");
		
		// We have to look through the complete program to find sources
		// which are then taken as seeds.
		int sinkCount = 0;
        logger.info("Looking for sources and sinks...");
        
        for (SootMethod thrunSM : getMethodsForSeeds(iCfg)){
			int result = scanMethodForSourcesSinks(ssm, forwardProblem, thrunSM);
        	sinkCount += result;
        }
		
		// Report on the sources and sinks we have found
        // KM: Like NullPointExceptions. There is no sinks for sink searching without detailed AccessPath.
//		if (!forwardProblem.hasInitialSeeds()) {
//			logger.error("No sources found, aborting analysis");
//			return;
//		}
//		if (sinkCount == 0) {
//			logger.error("No sinks found, aborting analysis");
//			return;
//		}
        
		logger.info("Preliminary source lookup done, found {} sources and {} sinks.", forwardProblem.getInitialSeeds().size(),
				sinkCount);
		
		// Initialize the taint wrapper if we have one
		if (taintWrapper != null)
			taintWrapper.initialize(manager); 
		if (nativeCallHandler != null)
			nativeCallHandler.initialize(manager);
		
		forwardSolver.solve();
		maxMemoryConsumption = Math.max(maxMemoryConsumption, getUsedMemory());
		
		// Not really nice, but sometimes Heros returns before all
		// executor tasks are actually done. This way, we give it a
		// chance to terminate gracefully before moving on.
		int terminateTries = 0;
		while (terminateTries < 10) {
			if (executor.getActiveCount() != 0 || !executor.isTerminated()) {
				terminateTries++;
				try {
					Thread.sleep(500);
				}
				catch (InterruptedException e) {
					logger.error("Could not wait for executor termination", e);
				}
			}
			else
				break;
		}
		if (executor.getActiveCount() != 0 || !executor.isTerminated())
			logger.error("Executor did not terminate gracefully");

		// Print taint wrapper statistics
		if (taintWrapper != null) {
			logger.info("Taint wrapper hits: " + taintWrapper.getWrapperHits());
			logger.info("Taint wrapper misses: " + taintWrapper.getWrapperMisses());
		}
		
		Set<AbstractionAtSink> res = forwardProblem.getResults();
		
		// We need to prune access paths that are entailed by another one
		for (Iterator<AbstractionAtSink> absAtSinkIt = res.iterator(); absAtSinkIt.hasNext(); ) {
			AbstractionAtSink curAbs = absAtSinkIt.next();
			for (AbstractionAtSink checkAbs : res)
				if (checkAbs != curAbs
						&& checkAbs.getSinkStmt() == curAbs.getSinkStmt()
						&& checkAbs.getAbstraction().isImplicit() == curAbs.getAbstraction().isImplicit())
					if (checkAbs.getAbstraction().getAccessPath().entails(
							curAbs.getAbstraction().getAccessPath())) {
						absAtSinkIt.remove();
						break;
					}
		}
		
		logger.info("IFDS problem with {} forward and {} backward edges solved, "
				+ "processing {} results...", forwardSolver.propagationCount,
				backSolver == null ? 0 : backSolver.propagationCount,
				res == null ? 0 : res.size());
		
		// Force a cleanup. Everything we need is reachable through the
		// results set, the other abstractions can be killed now.
		maxMemoryConsumption = Math.max(maxMemoryConsumption, getUsedMemory());
		forwardSolver.cleanup();
		if (backSolver != null) {
			backSolver.cleanup();
			backSolver = null;
			backProblem = null;
		}
		forwardSolver = null;
		forwardProblem = null;
		Runtime.getRuntime().gc();
		
		computeTaintPaths(res);		
		
		if (results == null || results.getResults().isEmpty())
			logger.warn("[KM-Results] No results found.");
		else for (ResultSinkInfo sink : results.getResults().keySet()) {
			Set<ResultSourceInfo> interestingSources = results.getResults().get(sink);
			interestingSources = new HashSet<ResultSourceInfo>(interestingSources);
			if(interestingSources == null || interestingSources.isEmpty())
				continue;
			if(checkForSourceSinkTypeMatch(sink, interestingSources).isEmpty())
				continue;
			if(checkForMultiThread(sink, interestingSources).isEmpty())
				continue;
			Map<ResultSourceInfo, Set<SootClass>> scExMap = checkForExceptionHandler(sink, interestingSources);
			if(scExMap == null){	//����null�����������Լ���publish��sink
				outputPublishSinkResults(sink, interestingSources);
				continue;
			}
			if(scExMap.isEmpty())
				continue;
			if(checkForPreExceptionChecker(sink, scExMap).isEmpty())	//�����ֱ�ӷ�Ӧ��scExMap��	
				continue;
			
			logger.info("[KM-Results] The sink {} in method {} was called with values from the following sources:",
                    sink, iCfg.getMethodOf(sink.getSink()).getSignature() );
			
			outputExceptionSinkResults(sink, scExMap);
		}
		
		for (ResultsAvailableHandler handler : onResultsAvailable)
			handler.onResultsAvailable(iCfg, results);
		
		if (config.getWriteOutputFiles())
			PackManager.v().writeOutput();
		
		maxMemoryConsumption = Math.max(maxMemoryConsumption, getUsedMemory());
		System.out.println("Maximum memory consumption: " + maxMemoryConsumption / 1E6 + " MB");
	}

	/**�������source��sink��type�Ƿ�ƥ�䣬Ȼ���������˶���Abstraction��tag���������ּ�鿴���ǲ���Ҫ���ˡ�
	 * TODO remove this!*/
	private Set<ResultSourceInfo> checkForSourceSinkTypeMatch(ResultSinkInfo sink, Set<ResultSourceInfo> interestingSources) {
//		MyAbstractionTag sinkTag = (MyAbstractionTag) sink.getSink().getTag(MyAbstractionTag.class.getSimpleName());
//		String sinkTypes = sinkTag.getSourceSinkType();
//		for(Object obj : interestingSources.toArray()){
//			ResultSourceInfo rsi = (ResultSourceInfo) obj;
//			Stmt sourceStmt = rsi.getSource();
//			MyAbstractionTag sourceTag = (MyAbstractionTag) sourceStmt.getTag(MyAbstractionTag.class.getSimpleName());
//			if(sourceTag == null)	//����������Ŀ�귽���Ĳ�����Ϊ��source��Ҳ����ȫ���͵�~
//				continue;
//			String sourceType = sourceTag.getSourceSinkType();
//			if(sinkTypes.contains(";" + sourceType + ";") || sinkTypes.startsWith(sourceType + ";"))
//				continue;
//			interestingSources.remove(rsi);
//		}
		return interestingSources;
	}

	private void outputExceptionSinkResults(ResultSinkInfo sink, Map<ResultSourceInfo, Set<SootClass>> scExMap) {
		Set<ResultSourceInfo> sourceSet = scExMap.keySet();
		for (ResultSourceInfo source : sourceSet) {
			String exceptionStr = "";
			for(SootClass sc : scExMap.get(source)){
				exceptionStr = exceptionStr + "; " + sc.getName();
			}
			
			logger.info("- {} in method {}",source, iCfg.getMethodOf(source.getSource()).getSignature());
			logger.info("-- Exceptions: " + exceptionStr.substring(2));
			
			if (source.getPath() == null) {
				continue;
			}
			logger.info("\ton Path: ");
			Stmt[] pathes = source.getPath();
			AccessPath[] aps = source.getPathAccessPaths();
			int size = pathes.length;
			for(int count = 0; count < size; count++){
				logger.info("\t -> " + iCfg.getMethodOf(pathes[count]));
				logger.info("\t\t -> AP: " + aps[count]);
				logger.info("\t\t -> PT: " + pathes[count]);
			}
		}
	}

	/**check every source and its exceptions one by one to find some pre-check code which can prevent those exceptions.
	 * TODO This part of work will be implemented by designing the IPathBuilderFactory of forward analysis.
	 * Every source will be tagged for potential exception types. During the forward analysis.
	 * If corresponding check for exceptions exits, corresponding source tag will be removed.
	 * And when my sink manager is called for isSink check, the source types will be considers.*/
	private Map<ResultSourceInfo, Set<SootClass>> checkForPreExceptionChecker(ResultSinkInfo sink, Map<ResultSourceInfo, Set<SootClass>> scExMap) {
		Set<ResultSourceInfo> sources = scExMap.keySet();
		for(ResultSourceInfo source : sources){
			Set<SootClass> exceptions = scExMap.get(source);
			for(Object obj : exceptions.toArray()){
				SootClass exc = (SootClass) obj;
				boolean checked = false;
				String clsName = exc.getName();
				switch(SourceSinkType.valueOf(SourceSinkType.class, clsName.substring(clsName.lastIndexOf(".") + 1))){
					case NullPointerException:	//TODO only nullpointer by now.
//						checked = checkNullPointerPrechecker(source, sink);
						break;
					default:
						break;
				}
				if(checked){
					exceptions.remove(exc);
					if(exceptions.isEmpty())
						scExMap.remove(source);
				}	
			}
		}
		return scExMap;
	}


//	private boolean checkNullPointerPrechecker(ResultSourceInfo source, ResultSinkInfo sink) {
//		if(aliasing == null)
//			aliasing = new Aliasing(aliasingStrategy, iCfg);
////			return false; 
//		
//		AccessPath apSource = source.getAccessPath();
//		AccessPath apSink = sink.getAccessPath();
//		if(apSource.isLocal()){
//			boolean myAlias = aliasing.mayAlias(apSource.getPlainValue(), apSink.getPlainValue()); 
//""			.toString();;
//		}
//		else if(apSource.getFieldCount() > 0){	//���ǵ�source��һ��ʼ����һ��field����ʽ����ͨ��������obj.field = null�����
//			SootField sourceFiled = apSource.getFirstField();
//			//apSinkĿǰ�����϶���һ��local���͵�ֵ��������Ϊ����ֱ�Ӷ���һ�����������ж�д����
//			//�����Ҫ������Ҫ$r0=obj.field������ת�����������Ҫ�ҵ����sink local��Ӧ��obj.field
//			for(Stmt ap : source.getPath()){
//				
//			}
//		}
//		
//		//�ҵ���ǰ��������֮ǰ������У������еı������Լ���Ա����Ŀ�ָ����
//		boolean checked = false;
//		AccessPath sinkedAP = sink.getAccessPath();
//		Stmt sinkStmt = sink.getSink();
//		//ͨ���۲����ɵ�jimple������Է��֣�ʹ��obj.field�Ĵ�����operateOn(obj.field)��
//		//��������һ����ʱ�м����������obj.field����$r1 = obj.field.
//		//��ˣ���һ������sinkedAP.getPlainValue()������Ч�Ĵ���sink�����۵�ֵ��
//		//�����ù������ڲ���Ĳ�������
//		checked = isNullPointerCheckedInMethod(sinkStmt, sinkedAP.getPlainValue());
//		return checked;
//	}
//
//	private boolean isNullPointerCheckedInMethod(Stmt targetStmt, Local targetLocal) {
//		List<Unit> preStmts = iCfg.getPredsOf(targetStmt);
//		Set<Local> als = new HashSet<Local>();
//		for(int i = 0; i < preStmts.size(); i++){
//			Stmt preStmt = (Stmt)preStmts.get(i);
//			if(isNullPointerCheckedInStmt(preStmt, targetLocal, als, targetStmt))
//				return true;
//		}
//		return false;
//	}
//
//	private boolean isNullPointerCheckedInStmt(Stmt stmt, Local targetValue, Set<Local> als, Stmt targetStmt) {
//		List<ValueBox> valueBoxes = stmt.getUseAndDefBoxes();
//		for(ValueBox vb : valueBoxes){
//			Value value = vb.getValue();
//			if(value instanceof Local)
//				if(aliasing.mustAlias((Local) value, targetValue, targetStmt))
//					als.add((Local) value);
//		}
//		
//		if(stmt instanceof IfStmt){
//			IfStmt ifstmt = (IfStmt) stmt;
//			Value expr = ifstmt.getCondition();
//			if(expr instanceof JEqExpr){
//				Value v1 = ((JEqExpr) expr).getOp1();
//				Value v2 = ((JEqExpr) expr).getOp2();
//				NullConstant nc = NullConstant.v();
//				if((v1.equals(nc) && als.contains(v2)) ||
//						(v2.equals(nc) && als.contains(v1)))
//					return true;
//			}
//			System.out.println();
//		}
//		
//		for(Unit preStmt : iCfg.getPredsOf(stmt)){
//			if( isNullPointerCheckedInStmt((Stmt) preStmt, targetValue, als, targetStmt))
//				return true;
//		}
//		return false;
//	}

	private Map<ResultSourceInfo, Set<SootClass>> checkForExceptionHandler(ResultSinkInfo sink,
			Set<ResultSourceInfo> intSources) {
		Map<ResultSourceInfo, Set<SootClass>> scExMap = new HashMap<ResultSourceInfo, Set<SootClass>>();
		Stmt sinkStmt = sink.getSink();
		
		MyStmtTag sinkTag = (MyStmtTag) sinkStmt.getTag(MyStmtTag.class.getSimpleName());
		Set<SourceSinkType> sinkTypes = sinkTag.getSinkTypes();
		sinkTypes.remove(SourceSinkType.MyTestPublish);	//���ǲ��ش������
		if(sinkTypes.size() == 1 && sinkTypes.contains(SourceSinkType.MyTestPublish))	
			return null;

		Set<SootClass> targetExceptions = new HashSet<SootClass>();		
		for(SourceSinkType st : sinkTypes){
			SootClass sc = Scene.v().getSootClass(st.getExceptionClassName());
			if(sc != null)
				targetExceptions.add(sc);
		}
		
		for(Object obj : intSources.toArray()){		//Ҳ���Ƕ�Ӧ�˴Ӹ���source�ִ�sink��·����ÿ��·����exception������ܲ�ͨŶ~
			Set<SootClass> tgExs = new HashSet<SootClass>(targetExceptions);
			ResultSourceInfo rsi = (ResultSourceInfo) obj;
			boolean interestingSource = true;
			
			//�跨֤���䲻interesting����������Ӧ���쳣����
			if(caughtInsideMethod(tgExs, sinkStmt))	//ȫ��catch�򲻸���Ȥ�ˣ�����catch��ֱ��Ӱ�쵽tgExs��
				interestingSource = false;
			else if(caughtOutsideMethod(tgExs, rsi.getPath().length - 2, rsi)) //ʵ�����Ǵ�sinkStmt֮ǰ���Ǹ������֤�Ƿ�ᱻcatch
				interestingSource = false;
			
			if(interestingSource)
				scExMap.put(rsi, tgExs);
			else
				intSources.remove(rsi);
		}
		return scExMap;
	}


	private boolean caughtOutsideMethod(Set<SootClass> targetExceptions, int pos, ResultSourceInfo rsi) {
		Stmt stmt = rsi.getPath()[pos];
		if(caughtInsideMethod(targetExceptions, stmt))
			return true;
		if(pos == 0)	//�����Ѿ����������һ��path��	
			return false;
		else
			return caughtOutsideMethod(targetExceptions, pos - 1, rsi);
	}

	private boolean caughtInsideMethod(Set<SootClass> targetExceptions, Stmt sinkStmt) {
		SootMethod sm = iCfg.getMethodOf(sinkStmt);
		ExceptionalUnitGraph graph = new ExceptionalUnitGraph(sm.getActiveBody());
		Collection<ExceptionDest> eds = graph.getExceptionDests(sinkStmt);
		for(ExceptionDest ed : eds){
			Trap trap = ed.getTrap();
			if(trap == null)
				continue;
			
			SootClass caughtEx = trap.getException();
			SootClass ex = Scene.v().getSootClass("java.lang.Exception");
			if(caughtEx.equals(ex)){
				targetExceptions.clear();
				break;
			}
			
			for(Object obj : targetExceptions.toArray()){
				SootClass targetEx = (SootClass) obj;
				boolean isCaught = false;
				for(SootClass sc = targetEx; !sc.equals(ex); sc = sc.getSuperclass()){
					if(sc.equals(caughtEx)){
						isCaught = true;
						break;
					}
				}
				if(isCaught)
					targetExceptions.remove(targetEx);
			}
		}
		return targetExceptions.isEmpty();
	}


	private void outputPublishSinkResults(ResultSinkInfo sink, Set<ResultSourceInfo> interestingResults) {
		//TODO output the MySourceSinkTag.sourceActiveInvokeTree if exist.
		
		for (ResultSourceInfo source : interestingResults) {
			logger.info("- {} in method {}",source, iCfg.getMethodOf(source.getSource()).getSignature());
			if (source.getPath() == null) {
				continue;
			}
			logger.info("\ton Path: ");
			Stmt[] pathes = source.getPath();
			AccessPath[] aps = source.getPathAccessPaths();
			int size = pathes.length;
			for(int count = 0; count < size; count++){
				logger.info("\t -> " + iCfg.getMethodOf(pathes[count]));
				logger.info("\t\t -> AP: " + aps[count]);
				logger.info("\t\t -> PT: " + pathes[count]);
			}
		}
	}



	private Set<ResultSourceInfo> checkForMultiThread(ResultSinkInfo sink, Set<ResultSourceInfo> intSources) {
		for(Object obj : intSources.toArray()){
			ResultSourceInfo rsi = (ResultSourceInfo) obj;
			Stmt[] paths = rsi.getPath();
			int multiThreadCounter = 0;
			for(Stmt pt : paths){
				switch (checkStmtType(pt)){
					case StartMultiThread:
						multiThreadCounter++;
						break;
					case ReturnMultiThread:
						multiThreadCounter--;
						break;
					default:
						break;
				}
					
			}
			if(multiThreadCounter < 0)	
				intSources.remove(rsi);
			else if(multiThreadCounter == 0){
				Stmt sourceStmt = rsi.getSource();
				MyStmtTag sourceStmtTag = (MyStmtTag)sourceStmt.getTag(MyStmtTag.class.getSimpleName());
//				if(sourceTag == null)	//����������Ŀ�귽���Ĳ�����Ϊ��source��Ҳ����ȫ���͵�~����������ǲ�����ڱ��������̵߳������
//					intSources.remove(rsi);
				MyInvokeTree invokeTree = getMultiThreadInvokeTree(sourceStmt, true);
				if(invokeTree.head == null)
					intSources.remove(rsi);
				sourceStmtTag.setSourceActiveInvokeTree(invokeTree);
			}
		}
		return intSources;
	}
	
	private MyInvokeTree getMultiThreadInvokeTree(Stmt sourceStmt, boolean shouldFindMultThread) {
		SootMethod sm = iCfg.getMethodOf(sourceStmt);
		Collection<Unit> callerUnits = iCfg.getCallersOf(sm);	//���������˵���˴�Ϊ�յ�
		MyInvokeTree result = new MyInvokeTree();

		if(checkStmtType(sourceStmt) == StmtThreadType.StartMultiThread){
			shouldFindMultThread = false;
			result.head = sourceStmt;
		}
		
		//���findMultThreadΪfalse����Ӧ��������Ϊhead����������Ϊchield���м�¼
		for(Object obj : callerUnits.toArray()){
			Unit callerUnit = (Unit) obj;
			MyInvokeTree childTree = getMultiThreadInvokeTree((Stmt)callerUnit, shouldFindMultThread);
			if(!shouldFindMultThread)	//Ҳ�����Ѿ��ҵ������߳������㣬Ҫ�����е������ҵ�
				result.chields.add(childTree);
			else{	//Ҳ����˵Ҫ��childTree��ϣ�����ҵ����߳�������
				if(childTree.head != null){
					result.head = sourceStmt;
					result.chields.add(childTree);
				}
			}
		}
		return result;
	}

	private StmtThreadType checkStmtType(Stmt pt) {
		StmtThreadType tmp = StmtThreadType.None;
		SootMethod sm = null;
		if(pt instanceof InvokeStmt){
			tmp = StmtThreadType.StartMultiThread;
//			sm = iCfg.getCalleesOfCallAt(pt).iterator().next();
			sm = ((InvokeStmt) pt).getInvokeExpr().getMethod();
		}
		else if(iCfg.isExitStmt(pt)){
			tmp = StmtThreadType.ReturnMultiThread;
			sm = iCfg.getMethodOf(pt);
		}
		else
			return StmtThreadType.None;
		if(sm == null)
			return StmtThreadType.None;
		
		boolean multiMth = false;
		SootClass rnSC = Scene.v().getSootClass("java.lang.Runnable");
		SootClass thSC = Scene.v().getSootClass("java.lang.Thread");
		String tagName = MyMethodTag.class.getSimpleName();
		if(sm.hasTag(tagName) && ((MyMethodTag)sm.getTag(tagName)).isMultithread())
			multiMth = true;
		else if(sm.getSubSignature().equals("void run()")){
			SootClass sc = sm.getDeclaringClass();
			multiMth = (sc.equals(rnSC) ||
						sc.equals(thSC) ||
						sc.getSuperclass().equals(thSC) || 
						sc.getInterfaces().contains(rnSC));
		}
		
		if(multiMth)
			return tmp;
			
		return StmtThreadType.None;
	}



	/**
	 * Creates a new executor object for spawning worker threads
	 * @param numThreads The number of threads to use
	 * @return The generated executor
	 */
	private CountingThreadPoolExecutor createExecutor(int numThreads) {
		return new CountingThreadPoolExecutor
				(config.getMaxThreadNum() == -1 ? numThreads
						: Math.min(config.getMaxThreadNum(), numThreads),
				Integer.MAX_VALUE, 30, TimeUnit.SECONDS,
				new LinkedBlockingQueue<Runnable>());
	}

	private Collection<SootMethod> getMethodsForSeeds(IInfoflowCFG icfg) {
		List<SootMethod> seeds = new LinkedList<SootMethod>();
		// If we have a callgraph, we retrieve the reachable methods. Otherwise,
		// we have no choice but take all application methods as an approximation
		if (Scene.v().hasCallGraph()) {
			List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>(Scene.v().getEntryPoints());
			ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
			reachableMethods.update();
			for (Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext();)
				seeds.add(iter.next().method());
		}
		else {
			long beforeSeedMethods = System.nanoTime();
			Set<SootMethod> doneSet = new HashSet<SootMethod>();
			for (SootMethod sm : Scene.v().getEntryPoints())
				getMethodsForSeedsIncremental(sm, doneSet, seeds, icfg);
			logger.info("Collecting seed methods took {} seconds", (System.nanoTime() - beforeSeedMethods) / 1E9);
		}
		return seeds;
	}

	private void getMethodsForSeedsIncremental(SootMethod sm,
			Set<SootMethod> doneSet, List<SootMethod> seeds, IInfoflowCFG icfg) {
		assert Scene.v().hasFastHierarchy();
		if (!sm.isConcrete() || !sm.getDeclaringClass().isApplicationClass() || !doneSet.add(sm))
			return;
		seeds.add(sm);
		for (Unit u : sm.retrieveActiveBody().getUnits()) {
			Stmt stmt = (Stmt) u;
			if (stmt.containsInvokeExpr())
				for (SootMethod callee : icfg.getCalleesOfCallAt(stmt))
					getMethodsForSeedsIncremental(callee, doneSet, seeds, icfg);
		}
	}
	
	/**
	 * Scans the given method for sources and sinks contained in it. Sinks are
	 * just counted, sources are added to the InfoflowProblem as seeds.
	 * @param sourcesSinks The SourceSinkManager to be used for identifying
	 * sources and sinks
	 * @param forwardProblem The InfoflowProblem in which to register the
	 * sources as seeds
	 * @param m The method to scan for sources and sinks
	 * @return The number of sinks found in this method
	 */
	private int scanMethodForSourcesSinks(
			final ISourceSinkManager sourcesSinks,
			InfoflowProblem forwardProblem,
			SootMethod m) {
		int sinkCount = 0;
		if (m.hasActiveBody()) {
			// Check whether this is a system class we need to ignore
			final String className = m.getDeclaringClass().getName();
			if (config.getIgnoreFlowsInSystemPackages()
					&& SystemClassHandler.isClassInSystemPackage(className))
				return sinkCount;
			
			// Look for a source in the method. Also look for sinks. If we
			// have no sink in the program, we don't need to perform any
			// analysis
			PatchingChain<Unit> units = m.getActiveBody().getUnits();
			for (Unit u : units) {
				Stmt s = (Stmt) u;
				if (sourcesSinks.getSourceInfo(s, iCfg) != null) {
					forwardProblem.addInitialSeeds(u, Collections.singleton(forwardProblem.zeroValue()));
					logger.debug("Source found: {}", u);
				}
				if (sourcesSinks.isSink(s, iCfg, null)) {
		            logger.debug("Sink found: {}", u);
					sinkCount++;
				}
			}
		}
		return sinkCount;
	}
	
	/**
	 * Gets the memory used by FlowDroid at the moment
	 * @return FlowDroid's current memory consumption in bytes
	 */
	private long getUsedMemory() {
		Runtime runtime = Runtime.getRuntime();
		return runtime.totalMemory() - runtime.freeMemory();
	}
	

	/**
	 * Computes the path of tainted data between the source and the sink
	 * @param res The data flow tracker results
	 */
	protected void computeTaintPaths(final Set<AbstractionAtSink> res) {
		IAbstractionPathBuilder builder = this.pathBuilderFactory.createPathBuilder	//pathBuilderFactory���촦������Ϊtrue��
				(config.getMaxThreadNum(), iCfg);
   		builder.computeTaintPaths(res);
   		if (this.results == null)
   			this.results = builder.getResults();
   		else
   			this.results.addAll(builder.getResults());
    	builder.shutdown();
	}

}
