package soot.jimple.infoflow.android.test.droidBench;

import java.util.Iterator;
import java.util.Map;

import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.CHATransformer;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Targets;

public class MySceneTransformer extends SceneTransformer {
	CallGraph cg;
	@Override
	protected void internalTransform(String phaseName,
			Map<String, String> options) {
		CHATransformer.v().transform();
		SootClass a = Scene.v().getSootClass("de.ecspride.MainActivity");
		SootMethod tgt = a.getMethodByName("onCreate");
		cg = Scene.v().getCallGraph();
		String outputMark = "";
		printCallGraphFromMethod(tgt, outputMark);
	}
	
	private void printCallGraphFromMethod(SootMethod src, String outputMark) {
		if(outputMark.length() >= 5){
			System.out.println("[CG] [W] The method inovation depth has reached 5 levels. Stop going deeper!!! ");
			return;
		}
		Iterator<MethodOrMethodContext> targets = new Targets(cg.edgesOutOf(src));
		while (targets.hasNext()) {
			SootMethod tgt = (SootMethod)targets.next();
			System.out.println("[CG] " + outputMark + src + " may call " + tgt);
			if(tgt.toString().startsWith("<java.") || tgt.toString().startsWith("<javax.") ||	//对于Java类的代码
					tgt.equals(src))		//对于递归调用的方法
				continue;
			printCallGraphFromMethod(tgt, outputMark + "-");
		}
	}
}
