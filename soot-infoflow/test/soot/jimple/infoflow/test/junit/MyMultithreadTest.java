package soot.jimple.infoflow.test.junit;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import soot.jimple.infoflow.IInfoflow;

public class MyMultithreadTest extends JUnitTests{
	private static final String SOURCE_STRING_PWD = "<soot.jimple.infoflow.test.android.AccountManager: java.lang.String getPassword()>";

    @Test(timeout=300000)
    public void multiTest1(){
    	IInfoflow infoflow = initInfoflow();
    	List<String> epoints = new ArrayList<String>();
    	epoints.add("<soot.jimple.infoflow.test.MyMultiThreadTestCode: void testThreadWithField0a(java.lang.String)>");
    	epoints.add("<soot.jimple.infoflow.test.MyMultiThreadTestCode: void testThreadWithField0b(java.lang.String)>");
		infoflow.computeInfoflow(appPath, libPath, epoints, sources, sinks);
		checkInfoflow(infoflow, 2);
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, SOURCE_STRING_PWD));
    }
}
