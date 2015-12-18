package soot.jimple.infoflow.test.junit;

import java.util.List;

import heros.InterproceduralCFG;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.DefinitionStmt;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;

//Created by KAME, 20151111

public class MyMethodArgsSourceSinkManager implements ISourceSinkManager {
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
	public MyMethodArgsSourceSinkManager(boolean taintSubFields, List<String> targetMethodsList, List<String> sinksList){
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
//long id = Thread.currentThread().getId();
//System.out.println("[TSink-" + id + "] Method: " + cfg.getMethodOf(sCallSite));
//System.out.println("[TSink-" + id + "] Stmt:" + sCallSite);
		if (!sCallSite.containsInvokeExpr())
			return false;
//		SootMethod target = sCallSite.getInvokeExpr().getMethod();
		String targetMth = sCallSite.getInvokeExpr().getMethod().getSignature();
//System.out.println("[T] " + targetMth);
		boolean isSink = false;
		for(String sk : sinks)
			if(sk.equals(targetMth)){
				isSink = true;
				break;
			}
		return isSink;
//		if (isSink) {
////				&& sCallSite.getInvokeExpr().getArgCount() > 0) {
//			if (ap == null){
////System.out.println("[TSink-" + id + "] [!] This is a sink! AP: " + ap);
//				return true;
//			}
//			else if (ap.getPlainValue() == sCallSite.getInvokeExpr().getArg(0))	//!!!�˴���Ҫ���ã�
//				if (ap.isLocal() || ap.getTaintSubFields()){
////System.out.println("[TSink-" + id + "] [!] This is a sink! AP: " + ap);
//					return true;
//				}
//		}
//		return false;
	}

}
