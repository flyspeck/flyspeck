package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * wlog [disch]: vars / expr
 */
public class WlogNode extends TacticNode {
	// The tactics applied to the original goal after the subgoal is proved
	private final TacticNode thenTactic;
	// The subgoal
	private final ObjectNode obj;
	// Variables
	private final ArrayList<IdNode> vars;
	
	/**
	 * Default constructor
	 */
	public WlogNode(TacticNode thenTactic, ObjectNode obj, ArrayList<IdNode> vars) {
		// thenTactic could be null
		assert(obj != null);
		if (thenTactic == null)
			thenTactic = new TacticChainNode();
	
		this.thenTactic = thenTactic;
		this.obj = obj;
		this.vars = new ArrayList<IdNode>(vars);
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("wlog");
		
		str.append(" [" + thenTactic + "]");
		str.append(": ");
		
		int n = vars.size();
		for (int i = 0; i < n; i++) {
			str.append(vars.get(i));
			if (i < n - 1)
				str.append(", ");
		}
		
		str.append('/');
		str.append(obj);
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (obj.getType() != ObjectNode.TERM)
			throw new RuntimeException("wlog: TERM expected: " + obj);

		buffer.append('(');
		
		// subgoal
		obj.translate(buffer);

		// tactic
		buffer.append(" (term_tac (wlog_tac ");
		
		// then_tactic
		thenTactic.translate(buffer);

		// variables
		buffer.append('[');
		int n = vars.size();
		for (int i = 0; i < n; i++) {
			IdNode id = vars.get(i);
			buffer.append('`');
			buffer.append(id.getId());
			buffer.append('`');
			
			if (i < n - 1)
				buffer.append("; ");
		}
		buffer.append(']');
		buffer.append("))");
		
		buffer.append(')');
	}
	
}
