package com.kame.sootinfo.mta;

import java.io.File;
import java.io.IOException;
import java.util.List;

import com.kame.sootinfo.mta.myplugin.MyIPCManager;
import com.kame.sootinfo.mta.myplugin.MySourceSinkManager;
import com.kame.sootinfo.mta.myplugin.MyTaintPropagationHandler;
import com.kame.sootinfo.mta.myplugin.MyTaintWrapper;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.INativeCallHandler;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;

public class MTAScene {
	private MTAScene(){}
	private static MTAScene thisOnly;

	static public MTAScene v(){
		if(thisOnly == null){
			thisOnly = new MTAScene();
		}
		return thisOnly;
	}
	
	static public MTAScene reInit(){
		thisOnly = new MTAScene();
		return thisOnly;
	}
	
	/**Config for soot-infoflow*/
	private InfoflowConfiguration infoflowConfig = null;
	public InfoflowConfiguration getInfoflowConfig(){
		if(infoflowConfig == null)
			infoflowConfig = new InfoflowConfiguration();
		return infoflowConfig;
	}

	/**Start point of analysis*/
	private List<String> targetList;
	public List<String> getTargetList() {
		return targetList;
	}
	public void setTargetList(List<String> list){
		this.targetList = list;
	}

	/**Method signature for sinks*/
	private List<String> sinkMethodList;
	public List<String> getSinkMethodList() {
		return sinkMethodList;
	}
	public void setSinkMethodList(List<String> list){
		sinkMethodList = list;
	}

	/**Path of file which contains the signature of source sink methods*/
	private String sourceSinkFile;
	public void setSourceSinkFile(String s){
		sourceSinkFile = s;
	}
	
	/**Source sink manager object.*/
	private ISourceSinkManager ssm = null;
	public ISourceSinkManager getSourceSinkManager() {
		if(ssm == null)
			ssm = new MySourceSinkManager();
		return ssm;
	}
	
	private ITaintPropagationWrapper taintWrapper = null;
	public ITaintPropagationWrapper getTaintWrapper() {
		if(taintWrapper == null){
			File f = new File(sourceSinkFile);
			try {
				taintWrapper = new MyTaintWrapper(f);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
		return taintWrapper;
	}
	
	private TaintPropagationHandler taintPropagationHandler = null;
	public MyTaintPropagationHandler getTaintPropagationHandler(){
		if(taintPropagationHandler == null)
			taintPropagationHandler = new MyTaintPropagationHandler();
		return (MyTaintPropagationHandler) taintPropagationHandler;
	}
	
	private INativeCallHandler nativeCallHandler = null;
	public INativeCallHandler getNativeCallHandler(){
		if(nativeCallHandler == null)
			nativeCallHandler = new DefaultNativeCallHandler(); //TODO do we need extend it?	
		return nativeCallHandler;
	}

	private IIPCManager ipcManager = null;
	public IIPCManager getIPCManager() {
		if(ipcManager == null)
			ipcManager = new MyIPCManager();	//TODO Do we need to implement this?
		return ipcManager;
	}
}
