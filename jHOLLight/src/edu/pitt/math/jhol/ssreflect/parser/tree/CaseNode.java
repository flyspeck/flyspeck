package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * case 
 */
public class CaseNode extends TacticNode {
	/**
	 * Default constructor
	 */
	public CaseNode() {
	}
	
	@Override
	protected String getString() {
		return "case";
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("case");
	}
	
}
