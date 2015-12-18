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
package soot.jimple.infoflow.rifl;

import java.io.StringWriter;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import soot.jimple.infoflow.rifl.RIFLDocument.Assignable;
import soot.jimple.infoflow.rifl.RIFLDocument.Category;
import soot.jimple.infoflow.rifl.RIFLDocument.DomainAssignment;
import soot.jimple.infoflow.rifl.RIFLDocument.DomainSpec;
import soot.jimple.infoflow.rifl.RIFLDocument.FlowPair;
import soot.jimple.infoflow.rifl.RIFLDocument.JavaFieldSpec;
import soot.jimple.infoflow.rifl.RIFLDocument.JavaParameterSpec;
import soot.jimple.infoflow.rifl.RIFLDocument.JavaReturnValueSpec;
import soot.jimple.infoflow.rifl.RIFLDocument.SourceSinkSpec;

/**
 * Class for writing out RIFL-compliant data flow policies
 *
 * @author Steven Arzt
 */
public class RIFLWriter {

	private final RIFLDocument document;
	
	/**
	 * Creates a new instance of the {@link RIFLWriter} class
	 * @param document The document to write out
	 */
	public RIFLWriter(RIFLDocument document) {
		this.document = document;
	}
	
	public String write() {
		try {
			// Create a new document
			DocumentBuilderFactory documentBuilderFactory = DocumentBuilderFactory.newInstance();
			DocumentBuilder documentBuilder = documentBuilderFactory.newDocumentBuilder();
			
			Document document = documentBuilder.newDocument();
			Element rootElement = document.createElement("riflspec");
			document.appendChild(rootElement);
			
			writeInterfaceSpec(document, rootElement);
			writeDomains(document, rootElement);
			writeDomainAssignment(document, rootElement);
			writeFlowPolicy(document, rootElement);
			
			// Write it out
			StringWriter stringWriter = new StringWriter();
			
			TransformerFactory transformerFactory = TransformerFactory.newInstance();
			Transformer transformer = transformerFactory.newTransformer();
			DOMSource source = new DOMSource(document);
			StreamResult result = new StreamResult(stringWriter);
			transformer.transform(source, result);
			return stringWriter.toString();
		}
		catch (ParserConfigurationException ex) {
			throw new RuntimeException(ex);
		}
		catch (TransformerConfigurationException ex) {
			throw new RuntimeException(ex);
		} catch (TransformerException ex) {
			throw new RuntimeException(ex);
		}
	}

	/**
	 * Writes out the interface specification component of the RIFL document
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeInterfaceSpec(Document document, Element rootElement) {
		Element attackerIO = document.createElement("interfacespec");
		rootElement.appendChild(attackerIO);
		
		for (Assignable assign : this.document.getInterfaceSpec().getSourcesSinks()) {
			writeAssignable(assign, document, attackerIO);
		}
	}
	
	/**
	 * Writes out an assignable element the RIFL document
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeAssignable(Assignable assign, Document document, Element rootElement) {
		Element attackerIO = document.createElement("assignable");
		rootElement.appendChild(attackerIO);

		attackerIO.setAttribute("handle", assign.getHandle());
		writeSourceSinkSpec(assign.getElement(), document, attackerIO);
	}
	
	/**
	 * Writes out a source/sink specification object
	 * @param spec The source/sink specification to write out
	 * @param document The document in which to write the source/sink specification
	 * @param parentElement The parent element in the DOM tree. This must be
	 * <source> or <sink>
	 */
	private void writeSourceSinkSpec(SourceSinkSpec spec, Document document,
			Element parentElement) {
		Element containerElement = null;
		switch (spec.getType()) {
		case Source:
			containerElement = document.createElement("source");
			break;
		case Sink:
			containerElement = document.createElement("sink");
			break;
		case Category:
			containerElement = document.createElement("category");
			break;
		default:
			throw new RuntimeException("Invalid source/sink type");
		}
		parentElement.appendChild(containerElement);
		
		if (spec instanceof JavaParameterSpec)
			writeJavaParameterSpec((JavaParameterSpec) spec, document, containerElement);
		else if (spec instanceof JavaFieldSpec)
			writeJavaFieldSpec((JavaFieldSpec) spec, document, containerElement);
		else if (spec instanceof JavaReturnValueSpec)
			writeJavaReturnValueSpec((JavaReturnValueSpec) spec, document, containerElement);
		else if (spec instanceof Category)
			writeCategory((Category) spec, document, containerElement);
		else
			throw new RuntimeException("Unsupported source or sink specification type");
	}

	/**
	 * Writes out a source/sink specification object for Java method parameters
	 * @param spec The source/sink specification to write out
	 * @param document The document in which to write the source/sink specification
	 * @param parentElement The parent element in the DOM tree. This must be
	 * <source> or <sink>
	 */
	private void writeJavaParameterSpec(JavaParameterSpec spec,
			Document document, Element parentElement) {
		Element parameter = document.createElement("parameter");
		parentElement.appendChild(parameter);
		
		parameter.setAttribute("class", spec.getClassName());
		parameter.setAttribute("method", spec.getHalfSignature());
		parameter.setAttribute("parameter", Integer.toString(spec.getParamIdx()));
	}

	/**
	 * Writes out a source/sink specification object for Java static fields
	 * @param spec The source/sink specification to write out
	 * @param document The document in which to write the source/sink specification
	 * @param parentElement The parent element in the DOM tree. This must be
	 * <source> or <sink>
	 */
	private void writeJavaFieldSpec(JavaFieldSpec spec,
			Document document, Element parentElement) {
		Element parameter = document.createElement("field");
		parentElement.appendChild(parameter);
		
		parameter.setAttribute("class", spec.getClassName());
		parameter.setAttribute("field", spec.getFieldName());
	}
	
	/**
	 * Writes out a source/sink specification object for the return values of
	 * Java methods
	 * @param spec The source/sink specification to write out
	 * @param document The document in which to write the source/sink specification
	 * @param parentElement The parent element in the DOM tree. This must be
	 * <source> or <sink>
	 */
	private void writeJavaReturnValueSpec(JavaReturnValueSpec spec,
			Document document, Element parentElement) {
		Element parameter = document.createElement("returnvalue");
		parentElement.appendChild(parameter);
		
		parameter.setAttribute("class", spec.getClassName());
		parameter.setAttribute("method", spec.getHalfSignature());
	}

	/**
	 * Writes out a category specification object Java methods
	 * @param spec The source/sink specification to write out
	 * @param document The document in which to write the source/sink specification
	 * @param parentElement The parent element in the DOM tree. This must be
	 * <source> or <sink>
	 */
	private void writeCategory(Category category, Document document,
			Element parentElement) {
		Element categoryElement = document.createElement("category");
		parentElement.appendChild(categoryElement);
		
		categoryElement.setAttribute("name", category.getName());
		for (SourceSinkSpec element : category.getElements()) {
			writeSourceSinkSpec(element, document, categoryElement);
		}
	}
	
	/**
	 * Writes out the domains component of the RIFL document
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeDomains(Document document, Element rootElement) {
		Element domains = document.createElement("domains");
		rootElement.appendChild(domains);

		for (DomainSpec spec : this.document.getDomains())
			writeDomainSpec(spec, document, domains);
	}

	/**
	 * Writes out a domain specification object
	 * @param spec The domain specification to write out
	 * @param document The document in which to write the domain specification
	 * @param parentElement The parent element in the DOM tree.
	 */
	private void writeDomainSpec(DomainSpec spec, Document document, Element parentElement) {
		Element categoryDomain = document.createElement("domain");
		parentElement.appendChild(categoryDomain);		
		categoryDomain.setAttribute("name", spec.getName());
	}

	/**
	 * Writes out the domains assignments section of the RIFL document
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeDomainAssignment(Document document, Element rootElement) {
		Element domainAssignment = document.createElement("domainassignment");
		rootElement.appendChild(domainAssignment);

		for (DomainAssignment spec : this.document.getDomainAssignment())
			writeDomainAssignment(spec, document, domainAssignment);
	}

	/**
	 * Writes out a source or sink domain pair
	 * @param pair The domain assignment to write out
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeDomainAssignment(DomainAssignment pair,
			Document document, Element rootElement) {
		final Element pairElement = document.createElement("assign");
		rootElement.appendChild(pairElement);
		
		pairElement.setAttribute("handle", pair.getSourceOrSink().getHandle());
		pairElement.setAttribute("domain", pair.getDomain().getName());
	}
	
	/**
	 * Writes out the flow policy component of the RIFL document
	 * @param document The XML document in which to write
	 * @param rootElement The root element of the document
	 */
	private void writeFlowPolicy(Document document, Element rootElement) {
		Element flowPolicy = document.createElement("flowrelation");
		rootElement.appendChild(flowPolicy);

		for (FlowPair pair : this.document.getFlowPolicy())
			writeFlowPair(pair, document, flowPolicy);
	}

	/**
	 * Writes out a flow pair object for the use inside the flow policy
	 * @param pair The flow pair to write out
	 * @param document The document in which to write the flow pair
	 * @param parentElement The parent element in the DOM tree
	 */
	private void writeFlowPair(FlowPair pair, Document document, Element parentElement) {
		Element flowPair = document.createElement("flow");
		parentElement.appendChild(flowPair);
		
		flowPair.setAttribute("from", pair.getFirstDomain().getName());
		flowPair.setAttribute("to", pair.getSecondDomain().getName());
	}

	/**
	 * Gets the document associated with this writer
	 * @return The document associated with this writer
	 */
	public RIFLDocument getDocument() {
		return this.document;
	}
}
