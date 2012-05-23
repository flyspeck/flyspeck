package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * have [disch]: expr
 */
public class HaveNode extends TacticNode {
	// The tactics applied to the original goal after the subgoal is proved
	private final TacticNode thenTactic;
	// Bound variables in the term represented by the object
	private final ArrayList<String> binders;
	// The subgoal
	private final ObjectNode obj;
	// If true then MP_TAC is used
	private final boolean assignFlag;
	
	/**
	 * Default constructor
	 */
	public HaveNode(TacticNode thenTactic, ArrayList<String> binders, ObjectNode obj, boolean assignFlag) {
		// thenTactic could be null
		assert(obj != null);
		if (thenTactic == null)
			thenTactic = new TacticChainNode();
	
		this.thenTactic = thenTactic;
		this.obj = obj;
		this.assignFlag = assignFlag;
		this.binders = new ArrayList<String>();
		
		if (binders != null)
			this.binders.addAll(binders);
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
			buffer.append(" (term_tac (have_gen_tac ");
			
			// binders
			int n = binders.size();
			buffer.append('[');
			
			for (int i = 0; i < n; i++) {
				buffer.append('"');
				buffer.append(binders.get(i));
				buffer.append('"');
				if (i < n - 1)
					buffer.append("; ");
			}
			
			buffer.append(']');
			// tactic
			thenTactic.translate(buffer);
			
			buffer.append("))");
		}
		
		buffer.append(')');
	}
	
}
