package soot.jimple.infoflow.results.xml;

/**
 * Abstract base class for serialized source or sink information
 * 
 * @author Steven Arzt
 *
 */
class AbstractSerializedSourceSink {
	
	private final SerializedAccessPath accessPath;
	private final String statement;
	
	/**
	 * Creates a new instance of the AbstractSerializedSourceSink class
	 * @param ap The tainted access path at this source or sink
	 * @param statement The statement that represents this source or sink
	 */
	protected AbstractSerializedSourceSink(SerializedAccessPath ap,
			String statement) {
		this.accessPath = ap;
		this.statement = statement;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((accessPath == null) ? 0 : accessPath.hashCode());
		result = prime * result
				+ ((statement == null) ? 0 : statement.hashCode());
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
		AbstractSerializedSourceSink other = (AbstractSerializedSourceSink) obj;
		if (accessPath == null) {
			if (other.accessPath != null)
				return false;
		} else if (!accessPath.equals(other.accessPath))
			return false;
		if (statement == null) {
			if (other.statement != null)
				return false;
		} else if (!statement.equals(other.statement))
			return false;
		return true;
	}
	
	/**
	 * Gets the tainted access path at the current source or sink
	 * @return The tainted access path at the current source or sink
	 */
	public SerializedAccessPath getAccessPath() {
		return this.accessPath;
	}
	
	/**
	 * Gets the statement representing this source or sink
	 * @return The statement representing this source or sink
	 */
	public String getStatement() {
		return this.statement;
	}

}
