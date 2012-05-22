package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * case or elim
 */
public class CaseElimNode extends TacticNode {
	private final boolean elimFlag;
	
	/**
	 * Default constructor
	 */
	public CaseElimNode(boolean elimFlag) {
		this.elimFlag = elimFlag;
	}
	
	@Override
	protected String getString() {
		if (elimFlag)
			return "elim";
		return "case";
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (elimFlag)
			buffer.append("elim");
		else
			buffer.append("case");
	}
	
}
