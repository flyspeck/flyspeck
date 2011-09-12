package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * apply
 */
public class ApplyNode extends TacticNode {
	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("(DISCH_THEN MATCH_MP_TAC)");
	}
	
	@Override
	protected String getString() {
		return "apply";
	}


}
