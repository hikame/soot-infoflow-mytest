/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.test.junit;

import heros.InterproceduralCFG;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.IInfoflow;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.source.SourceInfo;

/**
 * Test cases for FlowDroid's interaction with non-standard source sink managers
 * 
 * @author Steven Arzt
 */
public class SourceSinkTests extends JUnitTests {

	private static final String sourceGetSecret = "<soot.jimple.infoflow.test.SourceSinkTestCode: soot.jimple.infoflow.test.SourceSinkTestCode$A getSecret()>";
	private static final String sourceGetSecret2 = "<soot.jimple.infoflow.test.SourceSinkTestCode: soot.jimple.infoflow.test.SourceSinkTestCode$B getSecret2()>";
	
	private static final String sinkAP = "<soot.jimple.infoflow.test.SourceSinkTestCode: void doleakSecret2(soot.jimple.infoflow.test.SourceSinkTestCode$A)>";

	/** 创建了一个ISourceSinkManager的实例化对象，给出了自定义的isSink，判定方法就是与sinkAP的值作比较*/
	private abstract class BaseSourceSinkManager implements ISourceSinkManager {		

		@Override
		public boolean isSink(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg,
				AccessPath ap) {
			if (!sCallSite.containsInvokeExpr())
				return false;
			SootMethod target = sCallSite.getInvokeExpr().getMethod();
			if ((target.getSignature().equals(sinkAP) || target.getSignature().equals(sink))
					&& sCallSite.getInvokeExpr().getArgCount() > 0) {
				if (ap == null)
					return true;
				else if (ap.getPlainValue() == sCallSite.getInvokeExpr().getArg(0))
					if (ap.isLocal() || ap.getTaintSubFields())
						return true;
			}
			return false;
		}
	}
	
	/** 基于上面声明的SourceSinkManager创建了一个类的对象，在其中给出了以getSecret为判定准则的getSourceInfo方法*/
	private final ISourceSinkManager getSecretSSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg) {
			if (sCallSite.containsInvokeExpr()			//包含了方法调用表达式
					&& sCallSite instanceof DefinitionStmt		//定义语句
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")) {	//判定方法名
				AccessPath ap = AccessPathFactory.v().createAccessPath(
						((DefinitionStmt) sCallSite).getLeftOp(), true);
				return new SourceInfo(ap);
			}
			return null;
		}
		
	};
	
	/** 基于上面声明的SourceSinkManager创建了一个类的对象，在其中给出了以getSecret及2为判定准则的getSourceInfo*/
	private final ISourceSinkManager getSecretOrSecret2SSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg) {
			if (sCallSite.containsInvokeExpr()
					&& sCallSite instanceof DefinitionStmt
					&& (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
							|| (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret2")))) {
				AccessPath ap = AccessPathFactory.v().createAccessPath(
						((DefinitionStmt) sCallSite).getLeftOp(), true);
				return new SourceInfo(ap);
			}
			return null;
		}
		
	};
	
	/** 基于上面声明的SourceSinkManager创建了一个类的对象，在其中给出了以getSecret为判定准则的getSourceInfo，且不污染其子域*/
	private final ISourceSinkManager noTaintSubFieldsSSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InterproceduralCFG<Unit, SootMethod> cfg) {
			if (sCallSite.containsInvokeExpr()
					&& sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")) {
				AccessPath ap = AccessPathFactory.v().createAccessPath(
						((DefinitionStmt) sCallSite).getLeftOp(), false);
				return new SourceInfo(ap);
			}
			return null;
		}
		
	};
	
	/** 实现了SourceSinkManager，将if语句作为sink，将currentTimeMillis方法调用作为source*/
	private final class ifAsSinkSSM implements ISourceSinkManager {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite,
				InterproceduralCFG<Unit, SootMethod> cfg) {
			if (sCallSite instanceof DefinitionStmt
					&& sCallSite.containsInvokeExpr()
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("currentTimeMillis")) {
				Value val = ((DefinitionStmt) sCallSite).getLeftOp();
				return new SourceInfo(AccessPathFactory.v().createAccessPath(val, true));
			}
			return null;
		}

		@Override
		public boolean isSink(Stmt sCallSite,
				InterproceduralCFG<Unit, SootMethod> cfg, AccessPath ap) {
			return sCallSite instanceof IfStmt;
		}
		
	}
	
	@Test(timeout = 300000)
	public void fieldTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testDataObject()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), getSecretSSM);
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret));
	}

	@Test(timeout = 300000)
	public void negativeFieldTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testDataObject()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void accessPathTypesTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testAccessPathTypes()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), getSecretOrSecret2SSM);
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret));
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret2));
	}

	@Test(timeout = 300000)
	public void sourceAccessPathTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSourceAccessPaths()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void sinkAccessPathTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSinkAccessPaths()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void sinkAccessPathTest2() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSinkAccessPaths2()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void ifAsSinkTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void ifAsSinkTest()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new ifAsSinkSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
	}
}
