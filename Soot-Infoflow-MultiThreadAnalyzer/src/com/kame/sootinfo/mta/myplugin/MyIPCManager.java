package com.kame.sootinfo.mta.myplugin;

import heros.InterproceduralCFG;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.infoflow.ipc.IIPCManager;

public class MyIPCManager implements IIPCManager {

	@Override
	public boolean isIPC(Stmt sCallSite,
			InterproceduralCFG<Unit, SootMethod> cfg) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void updateJimpleForICC() {
		// TODO Auto-generated method stub

	}

}
