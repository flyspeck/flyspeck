package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * apply
 */
public class ApplyNode extends TacticNode {
	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append("apply_tac");
	}
	
	@Override
	protected String getString() {
		return "apply";
	}


}
