package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Describes a section
 */
public class SectionNode extends Node {
	// If true then this command begins a new section, otherwise it ends the section
	private final boolean startFlag;
	
	// The name of the section
	private final String sectionName;
	
	
	/**
	 * Constructor
	 */
	public SectionNode(boolean startFlag, String sectionName) {
		this.startFlag = startFlag;
		this.sectionName = sectionName;
	}
	
	
	/**
	 * Returns true if this command starts a new section
	 * @return
	 */
	public boolean isStartSection() {
		return startFlag;
	}
	
	
	/**
	 * Returns the name of the section
	 */
	public String getName() {
		return sectionName;
	}
	

	@Override
	protected String getString() {
		if (startFlag)
			return "Section " + sectionName;
		else
			return "End " + sectionName;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (startFlag)
			buffer.append("Sections.begin_section ");
		else
			buffer.append("Sections.end_section ");
		
		buffer.append('"');
		buffer.append(sectionName);
		buffer.append('"');
	}
	
	
	@Override
	public String getRevertCommand() {
		if (startFlag)
			return "Sections.end_section " + '"' + sectionName + '"';
		else
			return null;
	}

}
