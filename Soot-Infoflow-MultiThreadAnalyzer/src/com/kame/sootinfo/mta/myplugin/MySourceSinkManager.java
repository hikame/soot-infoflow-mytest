package com.kame.sootinfo.mta.myplugin;

import java.util.ArrayList;
import java.util.List;

import com.kame.sootinfo.mta.tags.MySinkTag;

import heros.InterproceduralCFG;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.dexpler.DalvikThrowAnalysis;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;
import soot.tagkit.StringTag;
import soot.tagkit.Tag;
import soot.toolkits.exceptions.ThrowableSet;
import sun.security.x509.IssuingDistributionPointExtension;

public class MySourceSinkManager implements ISourceSinkManager {
	boolean taintSubFields = true;
	List<String> targetMethods = null; 
	List<String> sinks = null;
	
	public enum SinkType{
		MyTestPublish("MyTestPublish"),
		NullPointerException("java.lang.NullPointerException");
		
		private String name;
		private SinkType(String s){
			name = s;
		}
		
		public String getName(){
			return name;
		}
	}
	
	/**
	 * @param taintSubFields
	 * 用于设定TaintAccess中taintSubFields的值。
	 * @param targetMethodsList
	 * 给出的方法名的参数是污点值
	 * @param sinksList
	 * 给出的方法名是sink*/
	public MySourceSinkManager(boolean taintSubFields, List<String> targetMethodsList, List<String> sinksList){
		this.taintSubFields =  taintSubFields;
		this.targetMethods = targetMethodsList;
		this.sinks = sinksList;
	}
	
	@Override
	public SourceInfo getSourceInfo(Stmt sCallSite,
			InterproceduralCFG<Unit, SootMethod> cfg) {		
//参照jimple的格式，方法的参数在方法的实现代码中是通过左操作数为临时操作变量，右操作数为实参的形式进行表示的，这种情况下，为左操作数创建TaintedPath信息。
		String mth = cfg.getMethodOf(sCallSite).toString();
		boolean isTarget = false;
		for(String tm : targetMethods)
			if(tm.equals(mth)){
				isTarget = true;
			}
		if(isTarget == false)
			return null;
		if(!(sCallSite instanceof DefinitionStmt))
			return null;
		DefinitionStmt ds = (DefinitionStmt) sCallSite;
		if(!(ds.getRightOp() instanceof ParameterRef))
			return null;
		Value leftOp = ((DefinitionStmt) sCallSite).getLeftOp();
		AccessPath ap = AccessPathFactory.v().createAccessPath(
				leftOp, taintSubFields);
//System.out.println("[TSrc-" + id + "] [!] This is a source! AP: " + ap);
		return new SourceInfo(ap);
	}

	@Override
	public boolean isSink(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg,
			AccessPath ap) {
		boolean result = false;
		result = isPublishSink(sCallSite, cfg, ap);
		result = result || isNullPointExceptionSink(sCallSite, cfg, ap);
		return result;
	}

	public boolean isNullPointExceptionSink(Stmt stmt, InterproceduralCFG<Unit, SootMethod> cfg, AccessPath ap) {
		boolean result = false;
		List<ValueBox> boxes = stmt.getUseBoxes();
		for(ValueBox box : boxes){
//System.out.println(box.toString());
			Value val = box.getValue();
			if(val instanceof InstanceInvokeExpr){
				if(ap == null)
					return true;
				Value base = ((InstanceInvokeExpr) val).getBase();
				Local local = ap.getPlainValue();
				boolean isFieldResf = ap.isFieldRef();
				if(base.equals(local) && !isFieldResf)
					result = true;
				break;
			}
			if(val instanceof InstanceFieldRef){
				if(ap == null)
					return true;
				if(checkInstanceFieldRefAsSink(val, ap)){
					result = true;
					break;
				}
			}
		}
		
		if(result)
			addTagIfNeccesary(stmt, SinkType.NullPointerException);
		
		return result;
	}

	private Object addTagIfNeccesary(Stmt stmt, SinkType sinkType) {
		MySinkTag msTag = (MySinkTag) stmt.getTag("MySinkTag");
		String type = sinkType.getName();
		if(msTag == null)
			stmt.addTag(new MySinkTag(type));
		else{
			String tagStr = msTag.getSinkType();
			boolean exist = tagStr.startsWith(sinkType + ";") || tagStr.contains(";" + type + ";");
			if(!exist){
				tagStr = tagStr + ";" + type;
				msTag.setSinkType(tagStr);
			}
		}
		return null;
	}

	public boolean checkInstanceFieldRefAsSink(Value val, AccessPath ap) {
		Value base = ((InstanceFieldRef)val).getBase();
		Local local = ap.getPlainValue();
		boolean isFieldResf = ap.isFieldRef();
		if(base.equals(local) && !isFieldResf)
			return true;
		return false;
	}

	private boolean isPublishSink(Stmt stmt, InterproceduralCFG<Unit, SootMethod> cfg, AccessPath ap) {
		if(!(stmt instanceof InvokeStmt))
			return false;
		InvokeStmt sCallSite = (InvokeStmt)stmt;
		String targetMth = sCallSite.getInvokeExpr().getMethod().getSignature();
		boolean isSink = false;
		for(String sk : sinks){
			if(sk.equals(targetMth)){
				if(ap == null){
					isSink = true;
					break;
				}
				
				Value param = sCallSite.getInvokeExpr().getArg(0);	//这个0不应是写死的！
				if(ap.getPlainValue().equals(param)){
					isSink = true;
					addTagIfNeccesary(stmt, SinkType.MyTestPublish);
					break;
				}
			}
		}
		return isSink;
	}

}
