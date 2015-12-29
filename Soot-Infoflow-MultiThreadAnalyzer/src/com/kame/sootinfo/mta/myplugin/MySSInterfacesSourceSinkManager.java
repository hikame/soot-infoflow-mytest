package com.kame.sootinfo.mta.myplugin;

import java.util.List;

import heros.InterproceduralCFG;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;
import soot.tagkit.StringTag;
import soot.tagkit.Tag;

public class MySSInterfacesSourceSinkManager implements ISourceSinkManager {
	boolean taintSubFields = true;
	List<String> targetMethods = null; 
	List<String> sinks = null;
//	private static final String sinkAP = "<soot.jimple.infoflow.test.SourceSinkTestCode: void doleakSecret2(soot.jimple.infoflow.test.SourceSinkTestCode$A)>";
//	protected static final String sink = "<soot.jimple.infoflow.test.android.ConnectionManager: void publish(java.lang.String)>";
	
	/**
	 * @param taintSubFields
	 * �����趨TaintAccess��taintSubFields��ֵ��
	 * @param targetMethodsList
	 * �����ķ������Ĳ������۵�ֵ
	 * @param sinksList
	 * �����ķ�������sink*/
	public MySSInterfacesSourceSinkManager(boolean taintSubFields, List<String> targetMethodsList, List<String> sinksList){
		this.taintSubFields =  taintSubFields;
		this.targetMethods = targetMethodsList;
		this.sinks = sinksList;
	}
	
	@Override
	public SourceInfo getSourceInfo(Stmt sCallSite,
			InterproceduralCFG<Unit, SootMethod> cfg) {
//long id = Thread.currentThread().getId();
//System.out.println("[TSrc-" + id + "] Method: " + cfg.getMethodOf(sCallSite));
//System.out.println("[TSrc-" + id + "] Stmt: " + sCallSite);
		
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
		AccessPath ap = AccessPathFactory.v().createAccessPath(
				((DefinitionStmt) sCallSite).getLeftOp(), taintSubFields);
//System.out.println("[TSrc-" + id + "] [!] This is a source! AP: " + ap);
		return new SourceInfo(ap);
	}

	@Override
	public boolean isSink(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg,
			AccessPath ap) {
		if (!sCallSite.containsInvokeExpr())	//�˴���ʱ������ôд����������Ҫ�����exception�����ӣ��˴�Ӧ������Ҫ���޸ĵ�
			return false;
		String targetMth = sCallSite.getInvokeExpr().getMethod().getSignature();
		boolean isSink = false;
		for(String sk : sinks)
			if(sk.equals(targetMth)){
				if(ap == null){
					isSink = true;
					break;
				}
				
				Value param = sCallSite.getInvokeExpr().getArg(0);	//���0��Ӧ��д���ģ�
				if(ap.getPlainValue().equals(param)){
					isSink = true;
					Tag newTag = createNewTag(sCallSite, "Sink-Pulisher");
					if(newTag != null)
						sCallSite.addTag(newTag);
					break;
				}
//				
//				if(!sCallSite.toString().equals("virtualinvoke $r1.<com.kame.tafhd.Publisher: void publish(java.lang.String)>($r3)"))
//					continue;
//				if(sCallSite.getTags().size() > 0)
//					System.out.println();
//				break;
			}
		
		if(isSink == false) {
			InvokeExpr ie = sCallSite.getInvokeExpr();
			if((ie instanceof InstanceInvokeExpr) && ap != null){
				Value base = ((InstanceInvokeExpr) ie).getBase();
				Local local = ap.getPlainValue();
				
				if(base.equals(local)){
					isSink = true;
					Tag newTag = createNewTag(sCallSite, "Sink-NullPointExcption");
					if(newTag != null)
						sCallSite.addTag(newTag);
				}
			}
		}
		return isSink;
	}

	private Tag createNewTag(Stmt sCallSite, String tagString) {
		List<Tag> currentTags = sCallSite.getTags();
		boolean exist = false;
		for(Tag tag : currentTags){
			if((tag instanceof StringTag) && ((StringTag) tag).getInfo().equals(tagString)){
				exist = true;
				break;
			}
		}
		if(exist)
			return null;
		return new StringTag(tagString);
	}

}
