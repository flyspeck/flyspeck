package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * have [disch]: expr
 */
public class HaveNode extends TacticNode {
	// The tactics applied to the original goal after the subgoal is proved
	private final TacticNode thenTactic;
	// The subgoal
	private final RawObjectNode subgoal;
	
	/**
	 * Default constructor
	 */
	public HaveNode(TacticNode thenTactic, RawObjectNode subgoal) {
		// thenTactic could be null
		assert(subgoal != null);
		if (thenTactic == null)
			thenTactic = new TacticChainNode();
		this.thenTactic = thenTactic;
		this.subgoal = subgoal;
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("have");
		
		if (thenTactic != null) {
			str.append(" [" + thenTactic + "]");
		}
		
		str.append(": ");
		str.append(subgoal);
		
		return str.toString();
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		// TODO: check if this is working
		thenTactic.beginTranslation(buffer, context);
		if (subgoal.getType() != ObjectNode.TERM)
			throw new RuntimeException("TERM expected: " + subgoal);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		// TODO: check
		thenTactic.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("(");
		buffer.append("SUBGOAL_THEN ");
		subgoal.translate(buffer);
		buffer.append("(fun th -> MP_TAC th THEN ");
		thenTactic.translate(buffer);
		buffer.append(")");
		buffer.append(")");
	}
	
}
