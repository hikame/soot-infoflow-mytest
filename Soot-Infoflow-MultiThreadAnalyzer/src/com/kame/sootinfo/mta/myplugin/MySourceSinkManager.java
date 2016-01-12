package com.kame.sootinfo.mta.myplugin;

import java.util.Arrays;
import java.util.List;
import java.util.Set;

import com.kame.sootinfo.mta.tags.MyStmtTag;

import heros.InterproceduralCFG;
import soot.Local;
import soot.PrimType;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;
import soot.kame.SourceSinkType;

public class MySourceSinkManager implements ISourceSinkManager {
	boolean taintSubFields = true;
	List<String> targetMethods = null; 
	List<String> sinks = null;
		
	/**
	 * @param taintSubFields
	 * 用于设定TaintAccess中taintSubFields的值。
	 * @param targetMethodsList
	 * 给出的方法名的参数是污点值
	 * @param sinksList
	 * 给出的方法名是sink*/
	public MySourceSinkManager(boolean taintSubFields, List<String> targetMethodsList, List<String> sinksList){
//		this.taintSubFields =  taintSubFields;
		this.targetMethods = targetMethodsList;
		this.sinks = sinksList;
	}
	
	@Override
	public SourceInfo getSourceInfo(Stmt stmt,
			InterproceduralCFG<Unit, SootMethod> cfg) {	
		//对于产生source的语句进行了tag标注
		SourceInfo result = isParameterOfTargetMethods(stmt, cfg);
		
		if(result == null)
			result = isNewNullValue(stmt, cfg);;	//查看是否可能引入新的空指，是则返回sourceinfo
		return result;
	}

	private SourceInfo isNewNullValue(Stmt stmt, InterproceduralCFG<Unit, SootMethod> cfg) {
		//TODO 还有一种情况没有考虑进去，就是当一个stmt是一个方法调用，而且可能会返回null的情况。
		//要求返回null的过程是可控的，那么从这个角度来说，只要能深入到方法源码中的话，还是可以直接分析出来的
		//麻烦的是对于我们设定为phtantom的类以及来自native方法，这种情况下也许需要我们手动配一些规则来实现。
		
		if(!(stmt instanceof DefinitionStmt))
			return null;
		DefinitionStmt ds = (DefinitionStmt) stmt;
		
		if(ds.getRightOp().equals(NullConstant.v())){
			Value leftOp = ((DefinitionStmt) stmt).getLeftOp();
			AccessPath ap = AccessPathFactory.v().createAccessPath(leftOp, false);
			Set<SourceSinkType> sourceTypes = ap.getSourceTypes();
			sourceTypes.add(SourceSinkType.NullPointerException);
			return new SourceInfo(ap);
		}
		return null;
	}

	private SourceInfo isParameterOfTargetMethods(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg) {
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
						leftOp, true);
				Set<SourceSinkType> sourceTypes = ap.getSourceTypes();
				sourceTypes.addAll(Arrays.asList(SourceSinkType.values()));
				if(leftOp.getType() instanceof PrimType)
					sourceTypes.remove(SourceSinkType.NullPointerException);
				return new SourceInfo(ap);
	}

	@Override
	public boolean isSink(Stmt sinkStmt, InterproceduralCFG<Unit, SootMethod> cfg,
			AccessPath ap) {
		//TODO sink是要根据sinkStmt中的MyStmtTag进行重新判定的
		boolean result = false;
		result = isPublishSink(sinkStmt, cfg, ap);
		result = result || isNullPointExceptionSink(sinkStmt, cfg, ap);
		return result;
	}

	public boolean isNullPointExceptionSink(Stmt stmt, InterproceduralCFG<Unit, SootMethod> cfg, AccessPath ap) {
		if(ap != null && !ap.getSourceTypes().contains(SourceSinkType.NullPointerException))
			return false;		
		boolean result = false;
		List<ValueBox> boxes = stmt.getUseBoxes();
		for(ValueBox box : boxes){
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
			addTagIfNeccesary(stmt, SourceSinkType.NullPointerException);
		
		return result;
	}

	private Object addTagIfNeccesary(Stmt stmt, SourceSinkType sinkType) {
		MyStmtTag msTag = (MyStmtTag) stmt.getTag(MyStmtTag.class.getSimpleName());
		if(msTag == null){
			MyStmtTag mst = new MyStmtTag();
			mst.getSinkTypes().add(sinkType);
			stmt.addTag(mst);
		}
		else
			msTag.getSinkTypes().add(sinkType);
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
		if(ap != null && !ap.getSourceTypes().contains(SourceSinkType.MyTestPublish))
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
					addTagIfNeccesary(stmt, SourceSinkType.MyTestPublish);
					break;
				}
			}
		}
		return isSink;
	}

}
