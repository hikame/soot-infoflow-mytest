package com.kame.sootinfo.mta;

import soot.SootClass;
import soot.Trap;
import soot.Unit;
import soot.jimple.internal.JTrap;

public class TrapInfo {
    /** The exception being caught. */
    public transient SootClass exception;

    /** The first unit being trapped. */
    public Unit beginUnit;

    /** The unit just before the last unit being trapped. */
    public Unit endUnit;

    /** The unit to which execution flows after the caught exception is triggered. */
    public Unit handlerUnit;

	public boolean isValid() {
		boolean result = (exception != null) && (beginUnit != null) && (endUnit != null);
		return result;
	}

	public Trap generateTrap() {
		return new JTrap(exception, beginUnit, endUnit, handlerUnit);
	}
}
