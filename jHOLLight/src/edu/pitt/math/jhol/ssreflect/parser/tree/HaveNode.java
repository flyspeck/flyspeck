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
	protected void translate(StringBuffer buffer) {
		if (!assignFlag && obj.getType() != ObjectNode.TERM)
			throw new RuntimeException("TERM expected: " + obj);
		
		buffer.append('(');
		obj.translate(buffer);
		
		if (assignFlag) {
			buffer.append(" (fun arg -> thm_tac MP_TAC arg THEN ");
			thenTactic.translate(buffer);
			buffer.append(')');
		}
		else {
			buffer.append(" (term_tac (have_tac ");
			thenTactic.translate(buffer);
			buffer.append("))");
		}
		
		buffer.append(')');
	}
	
}
