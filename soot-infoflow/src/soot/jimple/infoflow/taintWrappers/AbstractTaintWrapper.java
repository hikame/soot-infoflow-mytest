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
 * 所有自定义TainWrapper的父类
 * 关键在于继承并实现isExclusiveInternal和getTaintsForMethodInternal方法。
 * @author Steven Arzt
 */
public abstract class AbstractTaintWrapper implements ITaintPropagationWrapper {
	
	/**
	 * Data flow manager that gives access to internal solver objects
	 * 整个分析过程的管理者
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
	 * 这是一个内部实现函数，其将会通过本类中的isExclusive对外提供服务
	 * 获知是否一个taintwrapper产生的污点是唯一的。
	 * 也即除了wrapper产生的污点信息是可信的、可靠的，不需要额外分析的。
	 * 实际上这会用来指导分析过程不要进入到调用函数内部去运行。
	 * @param stmt The call statement to check
	 * @param taintedPath The tainted field or value to propagate
	 * @return True if this taint wrapper is exclusive, otherwise false. 
	 */
	protected abstract boolean isExclusiveInternal(Stmt stmt, AccessPath taintedPath);

	/**
	 * Checks an invocation statement for black-box taint propagation. This allows
	 * the wrapper to artificially propagate taints over method invocations without
	 * requiring the analysis to look inside the method.
	 * 这是一个内部实现函数，其将会通过本类中的isExclusive对外提供服务。实际上该类应该标记为protected或者private的。
	 * 给出一个方法调用前后的污点传播关系。
	 * 感觉是Wrapper真正实现的位置。
	 * 方法的内部相当于是一个黑盒的，通过该方法可以在不给出方法内部实现的情况下，进行污点传播的分析判断。
	 * 当然这一过程需要大量的人工干预。
	 * 
	 * @param stmt The invocation statement which to check for black-box taint propagation
	 * @param taintedPath The tainted field or value to propagate
	 * @return The list of tainted values after the invocation statement referenced in {@link Stmt}
	 * has been executed
	 */
	public abstract Set<AccessPath> getTaintsForMethodInternal(Stmt stmt, AccessPath taintedPath);

	
	/**调用的是内部方法实现的具体功能，此处做了封装，进行了hit和miss的统计工作*/
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
	
	/** 关键功能是调用的相应内部方法。
	 * 此函数将返回的AccessPath的集合转化为了Abstraction的集合。*/
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
