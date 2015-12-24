package com.kame.sootinfo.mta;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.IdentityUnit;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.Ref;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;
import soot.jimple.VirtualInvokeExpr;
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
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Units;
import soot.options.Options;

public class MyCFGParser {
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
	
	public void start() throws Exception{
		generateCFG();
	}

	private void generateCFG() {
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
