package com.kame.sootinfo.mta.myplugin;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.kame.sootinfo.mta.ControlFlowGraphManager;
import com.kame.sootinfo.mta.InfoflowAnalyzer;

import soot.Local;
import soot.Unit;
import soot.Value;
import soot.jimple.ConditionExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.EqExpr;
import soot.jimple.IfStmt;
import soot.jimple.NeExpr;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.solver.IMemoryManager;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.kame.SourceSinkType;

public class MyTaintPropagationHandler implements TaintPropagationHandler {
	Map<Abstraction, Set<Abstraction>> childrenMap = new HashMap<Abstraction, Set<Abstraction>>();
	
	Aliasing aliasing = null;
	private Aliasing getAliasing(){
		if(aliasing == null)
			aliasing = new Aliasing(
					InfoflowAnalyzer.v().getAliasing(), 
					ControlFlowGraphManager.v().getInfoflowCFG());
		return aliasing;
	}
	private IMemoryManager<Abstraction> memoryManager;
	@Override
	public Abstraction notifyFlowIn(Unit stmt, Abstraction taint, IInfoflowCFG cfg, FlowFunctionType type) {
//		Map<Stmt, Set<SourceSinkType>> taint.getAccessPath().getSourceTypeReduceMap()
		
		Map<Stmt, Set<SourceSinkType>> map = taint.getAccessPath().getSourceTypeReduceMapDirectly();
		if(map == null)
			return taint;
		Set<SourceSinkType> set = map.get(stmt);
		if(set == null || set.isEmpty())
			return taint;
		AccessPath ap = taint.getAccessPath();
		AccessPath newAP = ap.clone();
		newAP.getSourceTypes().removeAll(set);
		Abstraction result = taint.deriveNewAbstraction(newAP, (Stmt) stmt);
		result = memoryManager.handleGeneratedMemoryObject(taint, result);
		return result;
	}

	@Override
	public Set<Abstraction> notifyFlowOut(Unit stmt, Abstraction d1, Abstraction incoming, Set<Abstraction> outgoing,
			IInfoflowCFG cfg, FlowFunctionType type) {
		if(outgoing != null){
			for(Object obj : outgoing.toArray()){
				Abstraction abs = (Abstraction) obj;
				if(abs.getAccessPath().getSourceTypes().isEmpty())
					outgoing.remove(abs);
			}
			if(outgoing.isEmpty())
				return outgoing;
		}
		
		if(type.equals(FlowFunctionType.NormalFlowFunction) && stmt instanceof IfStmt){
			//������Ҫ�鿴if����Ƿ��й���apֵ�ļ�⣬������������������������ɾ��ap�е�sourceType
			if(incoming.getAccessPath().getSourceTypes().contains(SourceSinkType.NullPointerException))
				checkNullChecker(d1, (IfStmt) stmt, incoming, outgoing, cfg);
		}
		
		else if(type.equals(FlowFunctionType.NormalFlowFunction) && stmt instanceof DefinitionStmt){	//��ͨ�ĸ�����䣬����child��parent�Ĵ���
			Value left = ((DefinitionStmt)stmt).getLeftOp();
			Value right = ((DefinitionStmt)stmt).getRightOp();
			AccessPath rightAliasing = getAliasing().mayAlias(incoming.getAccessPath(), right);
			if(rightAliasing != null){
				Abstraction outAbs = null;
				for(Abstraction out : outgoing){
					if(getAliasing().mayAlias(out.getAccessPath(), left) != null){
						outAbs = out;
						break;
					}
				}
				if(outAbs != null){
					putIntoChildrenMap(incoming, outAbs);
				}
			}
		}
		
		else if(type.equals(FlowFunctionType.ReturnFlowFunction)){	//���βε�ʵ�εĴ���
			if(stmt instanceof ReturnStmt){
				Value retValue = ((ReturnStmt) stmt).getOpBox().getValue();
				if(getAliasing().mayAlias(incoming.getAccessPath(), retValue) != null){
					if((retValue instanceof Local) && outgoing.size() == 1){
						putIntoChildrenMap(incoming, outgoing.iterator().next());
					}
				}
			}
		}
		else if(type.equals(FlowFunctionType.CallFlowFunction)){
			if(incoming.getAccessPath().isLocal())
				putIntoChildrenMap(incoming, outgoing.iterator().next());
			else if(incoming.getAccessPath().isFieldRef() && incoming.getAccessPath().getPlainValue() != null && outgoing.size() == 1){
				putIntoChildrenMap(incoming, outgoing.iterator().next());
				Abstraction out = outgoing.iterator().next();
				synchronized(childrenMap){					
					Set<Abstraction> children = childrenMap.get(incoming);
					if(children != null && !children.isEmpty()){
						Set<Abstraction> outChildren = getMapValueSafely(out);
						for(Abstraction child : children)
							if(!child.equals(out))
								outChildren.add(child);
					}
						
				}
			}
		}
		return outgoing;
	}

	private void putIntoChildrenMap(Abstraction parent, Abstraction newChild) {
		if(parent.equals(newChild))
			return;
		synchronized(childrenMap){
			Set<Abstraction> children = getMapValueSafely(parent);
			children.add(newChild);
		}
	}

	private Set<Abstraction> getMapValueSafely(Abstraction parent) {
		Set<Abstraction> children = childrenMap.get(parent);
		if(children == null){
			children = new HashSet<Abstraction>();
			childrenMap.put(parent, children);
		}
		return children;
	}

	private void checkNullChecker(Abstraction d1, IfStmt ifstmt, Abstraction incoming, Set<Abstraction> outgoing, IInfoflowCFG cfg) {
		AccessPath ap = incoming.getAccessPath();
		ConditionExpr condition = (ConditionExpr)ifstmt.getCondition();
		Stmt targetStmt = null;
		if(condition instanceof EqExpr){
			List<Unit> succsUnits = cfg.getSuccsOf(ifstmt);
			if(succsUnits.size() == 1)
				targetStmt = (Stmt) succsUnits.get(0);
			else{
				if(succsUnits.size() == 2){
					int iftPos = succsUnits.indexOf(ifstmt.getTarget());
					targetStmt = (Stmt) succsUnits.get(1 - iftPos);
				}
				else{
					Stmt nextUnit = (Stmt) cfg.getMethodOf(ifstmt).getActiveBody().getUnits().getSuccOf(ifstmt);
					assert succsUnits.contains(nextUnit);
					targetStmt = nextUnit;
				}
			}
		}
		else if(condition instanceof NeExpr){
			targetStmt = ifstmt.getTarget();
		}
		else
			return;

		Value op1 = condition.getOp1();
		Value op2 = condition.getOp2();
		Value checkedValue = null;
		Value nullConstant = NullConstant.v();
		if(op1.equals(nullConstant))
			checkedValue = op2;
		else if(op2.equals(nullConstant))
			checkedValue = op1;
		if(checkedValue == null)
			return;
		
		//TODO ��һ�ּ�Ϊ�����������ܱ��ϼ��ĳ���
		/* sinkedValue = tainted.field;
		 * checkedValue = tainted.field;
		 * if(check on checkedValue)
		 *     doSink(sinkedValue);
		 * ����sinkedValue��checkedValue��ͬ��local�Ĳ��ֺܺü�飬��������Ķ������tainted.fieldת��Ϊ��tmp localʱ
		 * ����ͨ����¼tainted.field�������������������۵����ݼ�¼Abstraction�Ķ��󣬲�ͨ��ƥ����Щ�Ӽ�¼�뱻�����ֵ�Ƿ��Ǳ�����ϵ
		 * ʵ�ֶ���tainted.field����ж������ļ�¼��
		 */
		if(checkForSameLocal(incoming, outgoing, checkedValue, targetStmt))
			return;
		if(checkForSameField(incoming, checkedValue, targetStmt))
			return;
		return;
	}

	private boolean checkForSameField(Abstraction incoming, Value checkedValue,
			Stmt targetStmt) {
		//TODO �˴���Ҫ�����е������۵㴫���̶߳�����˴����У���������û�������̼߳�ͬ�����ƣ�
		// �ر��ǻ����ź������̼߳�ͬ����������ĳЩ�߳���Ҫ�ȴ������̱߳�ִ����ϲ��ܼ������е��¿���
		// ������ǳ��˽��м򵥵�sleep֮��Ҳ���������ˡ���
		try {
			Thread.sleep(100);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if(isAmongChildren(incoming, checkedValue, 0)){
			extendAPReduceMap(incoming, targetStmt, SourceSinkType.NullPointerException);
			return true;
		}
		return false;
	}

	private boolean isAmongChildren(Abstraction incoming, Value checkedValue, int depth) {
		Object[] children = null;
		synchronized(childrenMap){
			Set<Abstraction> set = childrenMap.get(incoming);
			if(set == null || set.isEmpty()){
				return false;
			}
			children = set.toArray();
		}
		
		for(Object obj : children){
			Abstraction child = (Abstraction) obj;
			if(getAliasing().mayAlias(child.getAccessPath(), checkedValue) != null)
				return true;
		}
		
		if(depth > 10)	//TODO This is incase of circel of invocation.
			return false;
		for(Object obj : children){
			Abstraction child = (Abstraction) obj;
			if(isAmongChildren(child, checkedValue, depth + 1))
				return true;
		}
		return false;
	}

	private boolean checkForSameLocal(Abstraction incoming, Set<Abstraction> outgoing, Value checkedValue, Stmt targetStmt) {
		boolean isSameLocal = false;
		if(incoming.getAccessPath().isLocal() && checkedValue instanceof Local){	//��checked value��Abstraction incoming��ͬһ��local����
			if(incoming.getAccessPath().getPlainValue().equals(checkedValue))
				isSameLocal = true;
		}
		if(!isSameLocal)
			return false;
		if(outgoing.contains(incoming)){
			extendAPReduceMap(incoming, targetStmt, SourceSinkType.NullPointerException);
		}
		return true;
	}

	private void extendAPReduceMap(Abstraction incoming, Stmt targetStmt, SourceSinkType nullpointerexception) {
		Map<Stmt, Set<SourceSinkType>>  map = incoming.getAccessPath().getSourceTypeReduceMap();
		Set<SourceSinkType> set = map.get(targetStmt);
		if(set == null)
			set = new HashSet<SourceSinkType>();
		set.add(SourceSinkType.NullPointerException);
		map.put(targetStmt, set);
	}

	private boolean isSameLocal(Abstraction incoming, Value checkedValue) {
		if(incoming.getAccessPath().isLocal() && checkedValue instanceof Local){	//��checked value��Abstraction incoming��ͬһ��local����
			if(incoming.getAccessPath().getPlainValue().equals(checkedValue))
				return true;
		}
		return false;
	}

	public void setMemoryManager(IMemoryManager<Abstraction> mm) {
		this.memoryManager = mm;
	}
}
