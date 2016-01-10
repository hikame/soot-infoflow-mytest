package com.kame.sootinfo.mta.myplugin;

import java.util.Arrays;
import java.util.List;
import java.util.Set;

import com.kame.sootinfo.mta.tags.MyStmtTag;

import heros.InterproceduralCFG;
import soot.Local;
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
	 * �����趨TaintAccess��taintSubFields��ֵ��
	 * @param targetMethodsList
	 * �����ķ������Ĳ������۵�ֵ
	 * @param sinksList
	 * �����ķ�������sink*/
	public MySourceSinkManager(boolean taintSubFields, List<String> targetMethodsList, List<String> sinksList){
//		this.taintSubFields =  taintSubFields;
		this.targetMethods = targetMethodsList;
		this.sinks = sinksList;
	}
	
	@Override
	public SourceInfo getSourceInfo(Stmt stmt,
			InterproceduralCFG<Unit, SootMethod> cfg) {	
		//���ڲ���source����������tag��ע
		SourceInfo result = isParameterOfTargetMethods(stmt, cfg);
		
		if(result == null)
			result = isNewNullValue(stmt, cfg);;	//�鿴�Ƿ���������µĿ�ָ�����򷵻�sourceinfo
		return result;
	}

	private SourceInfo isNewNullValue(Stmt stmt, InterproceduralCFG<Unit, SootMethod> cfg) {
		//TODO ����һ�����û�п��ǽ�ȥ�����ǵ�һ��stmt��һ���������ã����ҿ��ܻ᷵��null�������
		//Ҫ�󷵻�null�Ĺ����ǿɿصģ���ô������Ƕ���˵��ֻҪ�����뵽����Դ���еĻ������ǿ���ֱ�ӷ���������
		//�鷳���Ƕ��������趨Ϊphtantom�����Լ�����native���������������Ҳ����Ҫ�����ֶ���һЩ������ʵ�֡�
		
		if(!(stmt instanceof DefinitionStmt))
			return null;
		DefinitionStmt ds = (DefinitionStmt) stmt;
		
		if(ds.getRightOp().equals(NullConstant.v())){
//			��Ҫ���۵㴦��ӱ�ǩ��
//			MyStmtTag sourceTag = MyStmtTag.getTagFrom(stmt);
//			sourceTag.getSourceTypes(ds.getLeftOp()).add(SourceSinkType.NullPointerException);
			Value leftOp = ((DefinitionStmt) stmt).getLeftOp();
			AccessPath ap = AccessPathFactory.v().createAccessPath(leftOp, false);
			Set<SourceSinkType> sourceTypes = ap.getSourceTypes();
			sourceTypes.add(SourceSinkType.NullPointerException);
			return new SourceInfo(ap);
		}
		return null;
	}

	private SourceInfo isParameterOfTargetMethods(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg) {
		//����jimple�ĸ�ʽ�������Ĳ����ڷ�����ʵ�ִ�������ͨ���������Ϊ��ʱ�����������Ҳ�����Ϊʵ�ε���ʽ���б�ʾ�ģ���������£�Ϊ�����������TaintedPath��Ϣ��
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
				
//				MyStmtTag sourceTag = MyStmtTag.getTagFrom(sCallSite);
//				sourceTag.getSourceTypes(leftOp).addAll(Arrays.asList(SourceSinkType.values()));
		//System.out.println("[TSrc-" + id + "] [!] This is a source! AP: " + ap);
				return new SourceInfo(ap);
	}

	@Override
	public boolean isSink(Stmt sinkStmt, InterproceduralCFG<Unit, SootMethod> cfg,
			AccessPath ap) {
		//TODO sink��Ҫ����sinkStmt�е�MyStmtTag���������ж���
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
				
				Value param = sCallSite.getInvokeExpr().getArg(0);	//���0��Ӧ��д���ģ�
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
