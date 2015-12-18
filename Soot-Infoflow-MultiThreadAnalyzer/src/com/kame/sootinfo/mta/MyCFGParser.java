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

public class MyCFGParser {
	protected final BiDirICFGFactory icfgFactory = new DefaultBiDiICFGFactory();
	private final Logger logger = LoggerFactory.getLogger(getClass());
	private final InfoflowConfiguration config;
	private final ISourceSinkManager ssm;
	private final ITaintPropagationWrapper taintWrapper;
	private IInfoflowCFG iCfg;
	
	public MyCFGParser(InfoflowConfiguration cf, ISourceSinkManager is, ITaintPropagationWrapper tw){
		config = cf;
		ssm = is;
		taintWrapper = tw;
	}
	
	public IInfoflowCFG getInfoflowCFG(){
		return iCfg;
	}
	
	public void start(){
		generateCFG();
	}
	
	private void generateCFG() {
        // Perform constant propagation and remove dead code
        if (config.getCodeEliminationMode() != CodeEliminationMode.NoCodeElimination) {
			long currentMillis = System.nanoTime();
			eliminateDeadCode(ssm);
			logger.info("Dead code elimination took " + (System.nanoTime() - currentMillis) / 1E9
					+ " seconds");
        }
        if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand)
        	logger.info("Callgraph has {} edges", Scene.v().getCallGraph().size());
        iCfg = icfgFactory.buildBiDirICFG(config.getCallgraphAlgorithm(),
        		config.getEnableExceptionTracking());
	}
	
	/**
	 * Runs all code optimizers 
	 * @param sourcesSinks The SourceSinkManager
	 */
	private void eliminateDeadCode(ISourceSinkManager sourcesSinks) {
		ICodeOptimizer dce = new DeadCodeEliminator();
		dce.initialize(config);
		dce.run(iCfg, Scene.v().getEntryPoints(), sourcesSinks, taintWrapper);
	}
}
