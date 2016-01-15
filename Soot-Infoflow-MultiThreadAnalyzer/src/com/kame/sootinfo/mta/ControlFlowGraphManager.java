package com.kame.sootinfo.mta;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Scene;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.cfg.BiDirICFGFactory;
import soot.jimple.infoflow.cfg.DefaultBiDiICFGFactory;
import soot.jimple.infoflow.codeOptimization.DeadCodeEliminator;
import soot.jimple.infoflow.codeOptimization.ICodeOptimizer;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;

public class ControlFlowGraphManager {
	static ControlFlowGraphManager thisOnly = null;
	static public ControlFlowGraphManager v(){
		if(thisOnly == null){
			thisOnly = new ControlFlowGraphManager();
		}
		return thisOnly;
	}
	
	static public ControlFlowGraphManager reInit(){
		thisOnly = new ControlFlowGraphManager();
		return thisOnly;
	}
	
	private final Logger logger = LoggerFactory.getLogger(getClass());
	
	private final InfoflowConfiguration config = MTAScene.v().getInfoflowConfig();
	private ISourceSinkManager ssm = MTAScene.v().getSourceSinkManager();
	private ITaintPropagationWrapper taintWrapper = MTAScene.v().getTaintWrapper();

	private IInfoflowCFG iCfg;
	
//	public ControlFlowGraphManager(InfoflowConfiguration cf, ISourceSinkManager is, ITaintPropagationWrapper tw){
//		config = cf;
//		ssm = is;
//		taintWrapper = tw;
//	}
	
	public IInfoflowCFG getInfoflowCFG(){
		return iCfg;
	}

	public void generateCFG() {
		iCfg = null;
        // Perform constant propagation and remove dead code
        if (config.getCodeEliminationMode() != CodeEliminationMode.NoCodeElimination) {
			long currentMillis = System.nanoTime();
			eliminateDeadCode(ssm);
			logger.info("Dead code elimination took " + (System.nanoTime() - currentMillis) / 1E9
					+ " seconds");
        }
        if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand)
        	logger.info("Callgraph has {} edges", Scene.v().getCallGraph().size());
        BiDirICFGFactory icfgFactory = new DefaultBiDiICFGFactory();
        iCfg = icfgFactory.buildBiDirICFG(config.getCallgraphAlgorithm(),
        		config.getEnableExceptionTracking());
	}
	
	ICodeOptimizer dce = null;
	private ICodeOptimizer getCodeOptimizer() {
		if(dce == null){
			dce = new DeadCodeEliminator();
			dce.initialize(config);
		}
		return dce;
	}
	
	/**
	 * Runs all code optimizers 
	 * @param sourcesSinks The SourceSinkManager
	 */
	public void eliminateDeadCode(ISourceSinkManager sourcesSinks) {
		ICodeOptimizer dce = getCodeOptimizer();
		dce.run(iCfg, Scene.v().getEntryPoints(), sourcesSinks, taintWrapper);
	}


}
