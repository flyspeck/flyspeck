package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * move
 */
public class MoveNode extends TacticNode {
	/**
	 * Default constructor
	 */
	public MoveNode() {
	}
	
	@Override
	protected String getString() {
		return "move";
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		// Beta normalization
		buffer.append("BETA_TAC");
	}
	
}
