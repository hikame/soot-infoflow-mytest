package soot.jimple.infoflow.data;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicInteger;

import soot.jimple.infoflow.solver.IMemoryManager;

/**
 * Memory manager implementation for FlowDroid
 * 
 * @author Steven Arzt
 *
 */
public class FlowDroidMemoryManager implements IMemoryManager<Abstraction> {
	
	/**
	 * Special class for encapsulating taint abstractions for a full equality
	 * check including those fields (predecessor, etc.) that are normally left
	 * out
	 * 
	 * @author Steven Arzt
	 *
	 */
	private class AbstractionCacheKey {
		
		private final Abstraction abs;
		
		public AbstractionCacheKey(Abstraction abs) {
			this.abs = abs;
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * abs.hashCode();
			result = prime * result + ((abs.getPredecessor() == null) ? 0 : abs.getPredecessor().hashCode());
			result = prime * result + ((abs.getCurrentStmt() == null) ? 0 : abs.getCurrentStmt().hashCode());
			result = prime * result + ((abs.getCorrespondingCallSite() == null) ? 0 : abs.getCorrespondingCallSite().hashCode());
			return result;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			AbstractionCacheKey other = (AbstractionCacheKey) obj;
			
			if (!abs.equals(other.abs))
				return false;
			if (abs.getPredecessor() != other.abs.getPredecessor())
				return false;
			if (abs.getCurrentStmt() != other.abs.getCurrentStmt())
				return false;
			if (abs.getCorrespondingCallSite() != other.abs.getCorrespondingCallSite())
				return false;
			
			return true;
		}		
		
	}
	
	private ConcurrentMap<AccessPath, AccessPath> apCache = new ConcurrentHashMap<>();
	private ConcurrentHashMap<AbstractionCacheKey, Abstraction> absCache = new ConcurrentHashMap<>();
	private AtomicInteger reuseCounter = new AtomicInteger();
	
	private final boolean tracingEnabled;
	private boolean useAbstractionCache = false;
	
	/**
	 * Constructs a new instance of the AccessPathManager class
	 */
	public FlowDroidMemoryManager() {
		this(false);
	}
	
	/**
	 * Constructs a new instance of the AccessPathManager class
	 * @param tracingEnabled True if performance tracing data shall be recorded
	 */	
	public FlowDroidMemoryManager(boolean tracingEnabled) {
		this.tracingEnabled = tracingEnabled;
	}
	
	/**
	 * Gets the cached equivalent of the given access path
	 * @param ap The access path for which to get the cached equivalent
	 * @return The cached equivalent of the given access path
	 */
	private AccessPath getCachedAccessPath(AccessPath ap) {
		AccessPath oldAP = apCache.putIfAbsent(ap, ap);
		if (oldAP == null)
			return ap;
		
		// We can re-use an old access path
		if (tracingEnabled && oldAP != ap)
			reuseCounter.incrementAndGet();
		return oldAP;
	}
	
	/**
	 * Gets a cached equivalent abstraction for the given abstraction if we have
	 * one, otherwise returns null
	 * @param abs The abstraction for which to perform a cache lookup
	 * @return The cached abstraction equivalent to the given one of it exists,
	 * otherwise null
	 */
	private Abstraction getCachedAbstraction(Abstraction abs) {
		Abstraction oldAbs = absCache.putIfAbsent(new AbstractionCacheKey(abs), abs);
		if (oldAbs != null && oldAbs != abs)
			if (tracingEnabled)
				reuseCounter.incrementAndGet();
		return oldAbs;
	}
	
	/**
	 * Gets the number of access paths that have been re-used through caching
	 * @return The number of access paths that have been re-used through caching
	 */
	public int getReuseCount() {
		return this.reuseCounter.get();
	}

	@Override
	public Abstraction handleMemoryObject(Abstraction obj) {
		if (useAbstractionCache) {
			// We check for a cached version of the complete abstraction
			Abstraction cachedAbs = getCachedAbstraction(obj);
			if (cachedAbs != null)
				return cachedAbs;
		}
		
		// We check for a cached version of the access path
		AccessPath newAP = getCachedAccessPath(obj.getAccessPath());
		obj.setAccessPath(newAP);
		return obj;
	}

	@Override
	public Abstraction handleGeneratedMemoryObject(Abstraction input,
			Abstraction output) {
		// We we just pass the same object on, there is nothing to optimize
		if (input == output)
			return output;
		
		// If the flow function gave us a chain of abstractions, we can
		// compact it
		Abstraction pred = output.getPredecessor();
		if (pred != null && pred != input)
			output.setPredecessor(input);
		
		// If the abstraction didn't change at all, we can use the old one
		if (input.equals(output)) {
			if (output.getCurrentStmt() == null
					|| input.getCurrentStmt() == output.getCurrentStmt())
				return input;
			if (input.getCurrentStmt() == null) {
				synchronized (input) {
					if (input.getCurrentStmt() == null) {
						input.setCurrentStmt(output.getCurrentStmt());
						input.setCorrespondingCallSite(output.getCorrespondingCallSite());
						return input;
					}
				}
			}
		}
		
		return output;
	}
	
	/**
	 * Sets whether the memory manager shall use the abstraction cache
	 * @param useAbstractionCache True if the abstraction cache shall be used,
	 * otherwise false
	 */
	public void setUseAbstractionCache(boolean useAbstractionCache) {
		this.useAbstractionCache = useAbstractionCache;
	}

}
