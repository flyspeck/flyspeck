package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * have [disch]: expr
 */
public class HaveNode extends TacticNode {
	// The tactics applied to the original goal after the subgoal is proved
	private final TacticNode thenTactic;
	// The subgoal
	private final ObjectNode obj;
	// If true then MP_TAC is used
	private final boolean assignFlag;
	
	/**
	 * Default constructor
	 */
	public HaveNode(TacticNode thenTactic, ObjectNode obj, boolean assignFlag) {
		// thenTactic could be null
		assert(obj != null);
		if (thenTactic == null)
			thenTactic = new TacticChainNode();
	
		this.thenTactic = thenTactic;
		this.obj = obj;
		this.assignFlag = assignFlag;
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("have");
		
		str.append(" [" + thenTactic + "]");

		if (assignFlag)
			str.append(" := ");
		else
			str.append(": ");

		str.append(obj);
		return str.toString();
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		thenTactic.beginTranslation(buffer, context);
		if (!assignFlag && obj.getType() != ObjectNode.TERM)
			throw new RuntimeException("TERM expected: " + obj);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		thenTactic.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		
		if (assignFlag) {
			buffer.append("MP_TAC ");
			obj.translate(buffer);
			buffer.append(" THEN ");
			thenTactic.translate(buffer);
		}
		else {
			buffer.append("SUBGOAL_THEN ");
			obj.translate(buffer);
			buffer.append("(fun th -> MP_TAC th THEN ");
			thenTactic.translate(buffer);
			buffer.append(")");
		}
		
		buffer.append(')');
	}
	
}
