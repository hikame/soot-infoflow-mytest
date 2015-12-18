package soot.jimple.infoflow.taintWrappers;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;

/**
 * Abstract base class for all taint propagation wrappers
 * �����Զ���TainWrapper�ĸ���
 * �ؼ����ڼ̳в�ʵ��isExclusiveInternal��getTaintsForMethodInternal������
 * @author Steven Arzt
 */
public abstract class AbstractTaintWrapper implements ITaintPropagationWrapper {
	
	/**
	 * Data flow manager that gives access to internal solver objects
	 * �����������̵Ĺ�����
	 */
	protected InfoflowManager manager;
	
	private final AtomicInteger wrapperHits = new AtomicInteger(0);
	private final AtomicInteger wrapperMisses = new AtomicInteger(0);
	
	@Override
	public void initialize(InfoflowManager manager) {
		this.manager = manager;
	}
	
	/**
	 * Gets whether the taints produced by this taint wrapper are exclusive, i.e. there are
	 * no other taints than those produced by the wrapper. In effect, this tells the analysis
	 * not to propagate inside the callee.
	 * ����һ���ڲ�ʵ�ֺ������佫��ͨ�������е�isExclusive�����ṩ����
	 * ��֪�Ƿ�һ��taintwrapper�������۵���Ψһ�ġ�
	 * Ҳ������wrapper�������۵���Ϣ�ǿ��ŵġ��ɿ��ģ�����Ҫ��������ġ�
	 * ʵ�����������ָ���������̲�Ҫ���뵽���ú����ڲ�ȥ���С�
	 * @param stmt The call statement to check
	 * @param taintedPath The tainted field or value to propagate
	 * @return True if this taint wrapper is exclusive, otherwise false. 
	 */
	protected abstract boolean isExclusiveInternal(Stmt stmt, AccessPath taintedPath);

	/**
	 * Checks an invocation statement for black-box taint propagation. This allows
	 * the wrapper to artificially propagate taints over method invocations without
	 * requiring the analysis to look inside the method.
	 * ����һ���ڲ�ʵ�ֺ������佫��ͨ�������е�isExclusive�����ṩ����ʵ���ϸ���Ӧ�ñ��Ϊprotected����private�ġ�
	 * ����һ����������ǰ����۵㴫����ϵ��
	 * �о���Wrapper����ʵ�ֵ�λ�á�
	 * �������ڲ��൱����һ���ںеģ�ͨ���÷��������ڲ����������ڲ�ʵ�ֵ�����£������۵㴫���ķ����жϡ�
	 * ��Ȼ��һ������Ҫ�������˹���Ԥ��
	 * 
	 * @param stmt The invocation statement which to check for black-box taint propagation
	 * @param taintedPath The tainted field or value to propagate
	 * @return The list of tainted values after the invocation statement referenced in {@link Stmt}
	 * has been executed
	 */
	public abstract Set<AccessPath> getTaintsForMethodInternal(Stmt stmt, AccessPath taintedPath);

	
	/**���õ����ڲ�����ʵ�ֵľ��幦�ܣ��˴����˷�װ��������hit��miss��ͳ�ƹ���*/
	@Override
	public boolean isExclusive(Stmt stmt, Abstraction taintedPath) {
		if (isExclusiveInternal(stmt, taintedPath.getAccessPath())) {
			wrapperHits.incrementAndGet();
			return true;
		}
		else {
			wrapperMisses.incrementAndGet();
			return false;
		}
	}
	
	/** �ؼ������ǵ��õ���Ӧ�ڲ�������
	 * �˺��������ص�AccessPath�ļ���ת��Ϊ��Abstraction�ļ��ϡ�*/
	@Override
	public Set<Abstraction> getTaintsForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		// Compute the tainted access paths
		Set<AccessPath> aps = getTaintsForMethodInternal(stmt,
				taintedPath.getAccessPath());
		if (aps == null || aps.isEmpty())
			return null;
		
		// Convert the access paths into full abstractions
		Set<Abstraction> res = new HashSet<Abstraction>(aps.size());
		for (AccessPath ap : aps)
			if (ap == taintedPath.getAccessPath())
				res.add(taintedPath);
			else
				res.add(taintedPath.deriveNewAbstraction(ap, stmt));
		return res;
	}

	@Override
	public int getWrapperHits() {
		return wrapperHits.get();
	}

	@Override
	public int getWrapperMisses() {
		return wrapperMisses.get();
	}
	
}
