package com.kame.sootinfo.mta.myplugin;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;

import heros.TwoElementSet;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.infoflow.taintWrappers.AbstractTaintWrapper;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;;

/**this is basically learned from EasyTaintWrapper*/
public class MyTaintWrapper extends AbstractTaintWrapper implements Cloneable {
	private final Logger logger = LoggerFactory.getLogger(getClass());
	/**method列表的按Class整合版。
	 * 数量最多*/
	private final Map<String, Set<String>> classList;
	
	/**
	 * method列表的按Class整合版。
	 * exclude应该被用以表示有些类被认为不会对污点值产生影响*/
	private final Map<String, Set<String>> excludeList;
	
	/**method列表的按Class整合版。
	 * 全部为一些类的clear方法
	 * 将会导致这个方法的this对象的污点值被清除*/
	private final Map<String, Set<String>> killList;
	
	/**应该是用于批量标定某些类的处理方法。
	 * 包含了一些包名前半部分的字符串，如org.apache.http. & android. & java.
	 * 应该是用来标注哪些包中的类是我们所支持的，
	 * classList中的class必须属于此处包含的包中*/
	private final Set<String> includeList;
	
	/**一套用以类似于Map的工具。
	 * 其中定义的load方法是在添加新的Key的时候自动生成其value的。
	 * 其中的值在多线程间操作也有效的
	 * 该对象在被调用unCheck的时候，会先查询已有记录，如没有，则调用此类中的load方法，获取并保留相应Value*/
	private LoadingCache<SootMethod, MethodWrapType> methodWrapCache = CacheBuilder.newBuilder().build
			(new CacheLoader<SootMethod, MethodWrapType>() {

				@Override
				public MethodWrapType load(SootMethod arg0) throws Exception {
					return getMethodWrapType(arg0.getSubSignature(), arg0.getDeclaringClass());
				}
				
			});
	/**In aggressive mode, we always taint the return value if the base object is tainted.
	 * 在aggressive模式下，总是把一个tainted对象的方法调用的返回值也标记为tainted。*/
	private boolean aggressiveMode = false;
	
	/** whether the equals() and hashCode() methods shall always be modeled, regardless of the target type.
	 * 用以标记equals和hashCode是否总是需要被建模。*/
	private boolean alwaysModelEqualsHashCode = true;
	
	/**
	 * The possible effects this taint wrapper can have on a method invocation
	 * 一个taint wrapper在方法调用是可能存在的效果的枚举
	 */
	private enum MethodWrapType {
		/**
		 * This method can create a new taint
		 * 产生新的污点
		 */
		CreateTaint,
		/**
		 * This method can kill a taint
		 * 消除一个污点，参考killList
		 */
		KillTaint,
		/**
		 * This method has been explicitly excluded from taint wrapping, i.e.,
		 * it neither creates nor kills taints even if the same method in the
		 * parent class or an interfaces does.
		 * 对污点没有任何影响 
		 */
		Exclude,
		/**
		 * This method has not been named in the taint wrapper configuration
		 * 在taintwrapper的配置中（includeList没有或者ClassList中没有）没有出现这个方法。
		 */
		NotRegistered
	}
	
	/**
	 * Creates a new instanceof the {@link EasyTaintWrapper} class. This
	 * constructor assumes that all classes are included and get wrapped.
	 * However, only the methods in the given map create new taints.
	 * （实际上就是其他几个list被创建了一些空的列表）
	 * 
	 * @param classList The method for which to create new taints. This
	 * is a mapping from class names to sets of subsignatures.
	 */
	public MyTaintWrapper(Map<String, Set<String>> classList){
		this(classList, new HashMap<String, Set<String>>(),
				new HashMap<String, Set<String>>(),
				new HashSet<String>());
	}
	
	public MyTaintWrapper(Map<String, Set<String>> classList,
			Map<String, Set<String>> excludeList) {
		this(classList, excludeList, new HashMap<String, Set<String>>(),
				new HashSet<String>());
	}

	public MyTaintWrapper(Map<String, Set<String>> classList,
			Map<String, Set<String>> excludeList,
			Map<String, Set<String>> killList) {
		this(classList, excludeList, killList, new HashSet<String>());
	}

	public MyTaintWrapper(Map<String, Set<String>> classList,
			Map<String, Set<String>> excludeList,
			Map<String, Set<String>> killList,
			Set<String> includeList) {
		this.classList = classList;
		this.excludeList = excludeList;
		this.killList = killList;
		this.includeList = includeList;
	}
	/**@param f 表示给出wrapper定义文档的文件路径*/
	public MyTaintWrapper(String f) throws IOException{
        this(new File(f));
    }

	/**@param f 表示给出wrapper定义文档的文件*/
	public MyTaintWrapper(File f) throws IOException{
		BufferedReader reader = null;
		try{
			FileReader freader = new FileReader(f);
			reader = new BufferedReader(freader);
			String line = reader.readLine();
			List<String> methodList = new LinkedList<String>();
			List<String> excludeList = new LinkedList<String>();
			List<String> killList = new LinkedList<String>();
			this.includeList = new HashSet<String>();
			while(line != null){
				if (!line.isEmpty() && !line.startsWith("%"))
					if (line.startsWith("~"))	//全部是method
						excludeList.add(line.substring(1));
					else if (line.startsWith("-"))	//全部是method，各种类的clear()方法
						killList.add(line.substring(1));
					else if (line.startsWith("^"))	//给出的文档中，此处跟的是^org.apache.http.和^android.和^java.，表示了很多类
						includeList.add(line.substring(1));
					else	//超大量的方法列表
						methodList.add(line);
				line = reader.readLine();
			}
			this.classList = SootMethodRepresentationParser.v().parseClassNames(methodList, true);
			this.excludeList = SootMethodRepresentationParser.v().parseClassNames(excludeList, true);
			this.killList = SootMethodRepresentationParser.v().parseClassNames(killList, true);
			logger.info("Loaded wrapper entries for {} classes and {} exclusions.", classList.size(), excludeList.size());
		}
		finally {
			if (reader != null)
				reader.close();
		}
	}
	
	public MyTaintWrapper(MyTaintWrapper taintWrapper) {
		this(taintWrapper.classList, taintWrapper.excludeList, taintWrapper.killList, taintWrapper.includeList);
	}
		
	@Override
	public Set<AccessPath> getTaintsForMethodInternal(Stmt stmt, AccessPath taintedPath) {
		if (!stmt.containsInvokeExpr())	//不是方法调用语句，返回
			return Collections.emptySet();
		
		final Set<AccessPath> taints = new HashSet<AccessPath>();
		final SootMethod method = stmt.getInvokeExpr().getMethod();
		
		// If the callee is a phantom class or has no body, we pass on the taint
		// 如果被调用的函数是一个虚函数或者没有函数体，就把污点值进行传递下去。
		// 之所以做这个传递，是因为，在FlowDroid的文档3.1.1中所描述的Call-to-return flow function
		// 描述了这种类似wrapper的污点传播规则：将this中的所有域的tainted信息和参数的污点信息都剔除
		if (method.isPhantom() || !method.hasActiveBody()) {
			// Exception: Tainted value is overwritten 如果污点值被函数调用重写了的话就不会去做操作了。
			if (!(!taintedPath.isStaticFieldRef()					//taintedPath不是一个静态域的引用，参见下一条条件分支
					&& stmt instanceof DefinitionStmt			//stmt是一个DefinitionStmt
					&& ((DefinitionStmt) stmt).getLeftOp() == taintedPath.getPlainValue())) //taintedPath即为左操作数
				taints.add(taintedPath);
		}
		
		// For the moment, we don't implement static taints on wrappers. Pass it on
		// not to break anything
		// 这意思应该是如果taintedPath是一个静态的引用，那么函数调用对污点将不起任何影响。
		if(taintedPath.isStaticFieldRef())
			return Collections.singleton(taintedPath);
		
		// Do we handle equals() and hashCode() separately?
		final String subSig = stmt.getInvokeExpr().getMethodRef().getSubSignature().getString();
		boolean taintEqualsHashCode = alwaysModelEqualsHashCode
				&& (subSig.equals("boolean equals(java.lang.Object)") || subSig.equals("int hashCode()"));
		
		// We need to handle some API calls explicitly as they do not really fit
		// the model of our rules
		// 对于特殊API（String.getChars）的调用做明确的定义
		if (!taintedPath.isEmpty()
				&& method.getDeclaringClass().getName().equals("java.lang.String")
				&& subSig.equals("void getChars(int,int,char[],int)"))
			return handleStringGetChars(stmt.getInvokeExpr(), taintedPath);
		
		// If this is not one of the supported classes, we skip it
		boolean isSupported = includeList == null || includeList.isEmpty();
		if (!isSupported)
			for (String supportedClass : this.includeList)
				if (method.getDeclaringClass().getName().startsWith(supportedClass)) {
					isSupported = true;
					break;
				}
		
		//includeList中不包含 && 不是aggressive模式 && 并不是要被处理的eaqual或hash方法
		if (!isSupported && !aggressiveMode && !taintEqualsHashCode)
			return taints;
		
		// Check for a cached wrap type，根据Method名，查知其WrapType
		final MethodWrapType wrapType = methodWrapCache.getUnchecked(method);
		
		//判定stmt是一个实例化对象的方法调用
		if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {	
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();			
			if (taintedPath.isEmpty()		//参考AccessPath中emptyAccessPath域的备注
					 || iiExpr.getBase().equals(taintedPath.getPlainValue())) {	//如果污点值是方法调用的Base对象（this对象）
				// If the base object is tainted, we have to check whether we must kill the taint
				if (wrapType == MethodWrapType.KillTaint)		//这在taintedPath为空的时候岂不是消除了0值？词句应该对this对象tainted情况而言的吧~
					return Collections.emptySet();
				
				// If the base object is tainted, all calls to its methods always return
				// tainted values
				if (stmt instanceof DefinitionStmt) {
					DefinitionStmt def = (DefinitionStmt) stmt;

					// Check for exclusions
					if (wrapType != MethodWrapType.Exclude)	//在taintedPath是empty的情况下，只要不是Exclude类型的方法，就会引入新的AccessPath，这样看来这个粒度是比较粗糙的~
						taints.add(AccessPathFactory.v().createAccessPath(def.getLeftOp(), true));
				}

				// If the base object is tainted, we pass this taint on
				taints.add(taintedPath);
			}
		}
				
		//if param is tainted && classList contains classname && if list. contains
		// signature of method -> add propagation
		if (isSupported && wrapType == MethodWrapType.CreateTaint) {
			// If we are inside a conditional, we always taint 是否在污点值决定的条件分支里（后面简称污点值条件分支）
			boolean doTaint = taintedPath.isEmpty();
			
			// Otherwise, we have to check whether we have a tainted parameter
			if (!doTaint)	//不在污点条件分支里
				for (Value param : stmt.getInvokeExpr().getArgs()) {
					if (param.equals(taintedPath.getPlainValue())) {		//检查每一个参数是否是taintedPath所表示的
						// If we call a method on an instance with a tainted parameter, this
						// instance (base object) and (if it exists) any left side of the
						// respective assignment is assumed to be tainted.
						// 如果用污点参数去调用一个方法，这个函数的this对象和赋值语句的左侧运算数都应被设置为tainted
						if (!taintEqualsHashCode) {	//hashCode和equals之前处理过了
							doTaint = true;
							break;
						}						
					}
				}
			//此处的doTaint表示在污点分支里面、或者某个参数为污点值（且调用函数不是）
			if (doTaint) {
				// If make sure to also taint the left side of an assignment
				// if the object just got tainted 
				if (stmt instanceof DefinitionStmt)
					taints.add(AccessPathFactory.v().createAccessPath(((DefinitionStmt) stmt).getLeftOp(), true));
				
				// Taint the base object
				if (stmt.getInvokeExprBox().getValue() instanceof InstanceInvokeExpr)
					taints.add(AccessPathFactory.v().createAccessPath(((InstanceInvokeExpr)
							stmt.getInvokeExprBox().getValue()).getBase(), true));
				
				// The originally tainted parameter or base object as such
				// stays tainted
				taints.add(taintedPath);
			}
		}
		
		return taints;
	}
	
	/**
	 * Explicitly handles String.getChars() which does not really fit our
	 * declarative model
	 * 如果String对象被污染，那么调用其getChars方法的
	 * @param invokeExpr The invocation of String.getChars()
	 * @param taintedPath The tainted access path
	 * @return The set of new taints to pass on in the taint propagation
	 */
	private Set<AccessPath> handleStringGetChars(InvokeExpr invokeExpr,
			AccessPath taintedPath) {
		// If the base object is tainted, the third argument gets tainted as
		// well
		if (((InstanceInvokeExpr) invokeExpr).getBase() == taintedPath.getPlainValue())
			return new TwoElementSet<AccessPath>(taintedPath,
					AccessPathFactory.v().createAccessPath(invokeExpr.getArg(2), true)); //public void getChars(int srcBegin, int srcEnd, char[] dst,  int dstBegin)
		return Collections.singleton(taintedPath);
	}

	/**
	 * Checks whether at least one method in the given class is registered in
	 * the taint wrapper
	 * @param parentClass The class to check
	 * @param newTaints Check the list for creating new taints
	 * @param killTaints Check the list for killing taints
	 * @param excludeTaints Check the list for excluding taints
	 * @return True if at least one method of the given class has been registered
	 * with the taint wrapper, otherwise
	 */
	private boolean hasWrappedMethodsForClass(SootClass parentClass,
			boolean newTaints, boolean killTaints, boolean excludeTaints) {
		if (newTaints && classList.containsKey(parentClass.getName()))
			return true;
		if (excludeTaints && excludeList.containsKey(parentClass.getName()))
			return true;
		if (killTaints && killList.containsKey(parentClass.getName()))
			return true;
		return false;
	}
	
	/**
	 * Gets the type of action the taint wrapper shall perform on a given method
	 * 
	 * @param subSig The subsignature of the method to look for
	 * @param parentClass The parent class in which to start looking
	 * @return The type of action to be performed on the given method
	 */
	private MethodWrapType getMethodWrapType(String subSig, SootClass parentClass) {
		// If this is not one of the supported classes, we skip it，确保在include list里面嘛~
		boolean isSupported = false;
		for (String supportedClass : this.includeList)
			if (parentClass.getName().startsWith(supportedClass)) {
				isSupported = true;
				break;
			}
		
		// Do we always model equals() and hashCode()? 如果是equals或hashCode，并且设置了相应标志，返回Create
		if (alwaysModelEqualsHashCode
				&& (subSig.equals("boolean equals(java.lang.Object)") || subSig.equals("int hashCode()")))
			return MethodWrapType.CreateTaint;
		
		// Do not process unsupported classes 
		if (!isSupported)
			return MethodWrapType.NotRegistered;
		
		if (parentClass.isInterface())		//对于接口方法的处理
			return getInterfaceWrapType(subSig, parentClass);
		else {
			// We have to walk up the hierarchy to also include all methods
			// registered for superclasses 
			List<SootClass> superclasses = Scene.v().getActiveHierarchy().getSuperclassesOfIncluding(parentClass);
			for(SootClass sclass : superclasses) {	//对于其每个祖先类中的该方法，进行WrapType的判定
				MethodWrapType wtClass = getMethodWrapTypeDirect(sclass.getName(), subSig);
				if (wtClass != MethodWrapType.NotRegistered)
					return wtClass;
				
				for (SootClass ifc : sclass.getInterfaces()) {	//如果其某个祖先类NotRegistered，还要去判定其祖先类所实现的所有接口中的该方法，进行WrapType的判定
					MethodWrapType wtIface = getInterfaceWrapType(subSig, ifc);
					if (wtIface != MethodWrapType.NotRegistered)
						return wtIface;
				}
			}
		}
		
		return MethodWrapType.NotRegistered;
	}
	
	/**
	 * Checks whether the taint wrapper has an entry for the given combination
	 * of class/interface and method subsignature. This method does not take the
	 * hierarchy into account.
	 * 
	 * 根据classList、excludeList、killList列表，返回MethodWrapType
	 *  
	 * @param className The name of the class to look for
	 * @param subSignature The method subsignature to look for
	 * @return The type of wrapping if the taint wrapper has been configured
	 * with the given class or interface name and method subsignature, otherwise
	 * NotRegistered.
	 */
	private MethodWrapType getMethodWrapTypeDirect(String className, String subSignature) {
		if (alwaysModelEqualsHashCode
				&& (subSignature.equals("boolean equals(java.lang.Object)") || subSignature.equals("int hashCode()")))
			return MethodWrapType.CreateTaint;

		Set<String> cEntries = classList.get(className);
		Set<String> eEntries = excludeList.get(className);
		Set<String> kEntries = killList.get(className);
		
		if (cEntries != null && cEntries.contains(subSignature))
			return MethodWrapType.CreateTaint;
		if (eEntries != null && eEntries.contains(subSignature))
			return MethodWrapType.Exclude;
		if (kEntries != null && kEntries.contains(subSignature))
			return MethodWrapType.KillTaint;
		return MethodWrapType.NotRegistered;
	}

	/**
	 * Checks whether the taint wrapper has been configured for the given method
	 * in the given interface or one of its parent interfaces. 
	 * @param subSig The method subsignature to look for
	 * @param ifc The interface where to start the search
	 * @return The configured type of wrapping if the given method is implemented
	 * in the given interface or one of its super interfaces, otherwise
	 * NotRegistered
	 */
	private MethodWrapType getInterfaceWrapType(String subSig, SootClass ifc) {
		if (ifc.isPhantom())	//是一个虚类
			return getMethodWrapTypeDirect(ifc.getName(), subSig);
				
		assert ifc.isInterface() : "Class " + ifc.getName() + " is not an interface, though returned "
				+ "by getInterfaces().";
		for (SootClass pifc : Scene.v().getActiveHierarchy().getSuperinterfacesOfIncluding(ifc)) {	//找到了该接口的所有父接口
			MethodWrapType wt = getMethodWrapTypeDirect(pifc.getName(), subSig);
			if (wt != MethodWrapType.NotRegistered)
				return wt;
		}
		return MethodWrapType.NotRegistered;
	}
	
	@Override
	public boolean isExclusiveInternal(Stmt stmt, AccessPath taintedPath) {
		SootMethod method = stmt.getInvokeExpr().getMethod();
		
		// Do we have an entry for at least one entry in the given class?
		// 如果有Wrapper，则为true
		if (hasWrappedMethodsForClass(method.getDeclaringClass(), true, true, true))
			return true;

		// In aggressive mode, we always taint the return value if the base
		// object is tainted.
		if (aggressiveMode && stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();			
			if (iiExpr.getBase().equals(taintedPath.getPlainValue()))
				return true;
		}
		
		final MethodWrapType wrapType = methodWrapCache.getUnchecked(method);
		return wrapType != MethodWrapType.NotRegistered;
	}
	
	/**
	 * Sets whether the taint wrapper shall always assume the return value of a
	 * call "a = x.foo()" to be tainted if the base object is tainted, even if
	 * the respective method is not in the data file.
	 * @param aggressiveMode True if return values shall always be tainted if
	 * the base object on which the method is invoked is tainted, otherwise
	 * false
	 */
	public void setAggressiveMode(boolean aggressiveMode) {
		this.aggressiveMode = aggressiveMode;
	}
	
	/**
	 * Gets whether the taint wrapper shall always consider return values as
	 * tainted if the base object of the respective invocation is tainted
	 * @return True if return values shall always be tainted if the base
	 * object on which the method is invoked is tainted, otherwise false
	 */
	public boolean getAggressiveMode() {
		return this.aggressiveMode;
	}
	
	/**
	 * Sets whether the equals() and hashCode() methods shall always be modeled,
	 * regardless of the target type.
	 * @param alwaysModelEqualsHashCode True if the equals() and hashCode()
	 * methods shall always be modeled, regardless of the target type, otherwise
	 * false
	 */
	public void setAlwaysModelEqualsHashCode(boolean alwaysModelEqualsHashCode) {
		this.alwaysModelEqualsHashCode = alwaysModelEqualsHashCode;
	}
	
	/**
	 * Gets whether the equals() and hashCode() methods shall always be modeled,
	 * regardless of the target type.
	 * @return True if the equals() and hashCode() methods shall always be modeled,
	 * regardless of the target type, otherwise false
	 */
	public boolean getAlwaysModelEqualsHashCode() {
		return this.alwaysModelEqualsHashCode;
	}
	
	/**
	 * Registers a prefix of class names to be included when generating taints.
	 * All classes whose names don't start with a registered prefix will be
	 * skipped.
	 * @param prefix The prefix to register
	 */
	public void addIncludePrefix(String prefix) {
		this.includeList.add(prefix);
	}
	
	/**
	 * Adds a method to which the taint wrapping rules shall apply
	 * @param className The class containing the method to be wrapped
	 * @param subSignature The subsignature of the method to be wrapped
	 */
	public void addMethodForWrapping(String className, String subSignature) {
		Set<String> methods = this.classList.get(className);
		if (methods == null) {
			methods = new HashSet<String>();
			this.classList.put(className, methods);
		}
		methods.add(subSignature);
	}
	
	@Override
	public MyTaintWrapper clone() {
		return new MyTaintWrapper(this);
	}

	@Override
	public boolean supportsCallee(SootMethod method) {
		// Be conservative in aggressive mode
		if (aggressiveMode)
			return true;
		
		// Check for special models
		final String subSig = method.getSubSignature();
		if (alwaysModelEqualsHashCode
				&& (subSig.equals("boolean equals(java.lang.Object)") || subSig.equals("int hashCode()")))
			return true;

		for (String supportedClass : this.includeList)
			if (method.getDeclaringClass().getName().startsWith(supportedClass))
				return true;
		return false;
	}
	
	@Override
	public boolean supportsCallee(Stmt callSite) {
		// We need an invocation expression
		if (!callSite.containsInvokeExpr())
			return false;

		SootMethod method = callSite.getInvokeExpr().getMethod();
		if (!supportsCallee(method))
			return false;
				
		// We need a method that can create a taint
		if (!aggressiveMode) {	//不是aggressive模式
			// Check for a cached wrap type
			final MethodWrapType wrapType = methodWrapCache.getUnchecked(method);
			if (wrapType != MethodWrapType.CreateTaint)	//不会创造污点
				return false;
		}
		
		// We need at least one non-constant argument or a tainted base
		//如果是实例化对象的方法调用，返回true
		if (callSite.getInvokeExpr() instanceof InstanceInvokeExpr)
			return true;
		//如果不是静态方法调用，并且至少有一个变量不为常量，返回true
		for (Value val : callSite.getInvokeExpr().getArgs())
			if (!(val instanceof Constant))
				return true;
		return false;
	}

	@Override
	public Set<Abstraction> getAliasesForMethod(Stmt stmt, Abstraction d1,
			Abstraction taintedPath) {
		// We do not provide any aliases
		return null;
	}
		
}
