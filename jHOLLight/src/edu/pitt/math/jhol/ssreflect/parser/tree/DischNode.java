package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * move: x
 */
public class DischNode extends TacticNode {
	// Specifies which terms must be generalized
	private final ArrayList<Integer> occs;
	// The object which is discharged
	private final ObjectNode obj;
	// Equality label
	private final String eqLabel;
	
	/**
	 * Default constructor
	 */
	public DischNode(ObjectNode obj, ArrayList<Integer> occs, String eqLabel) {
		assert(obj != null);
		
		this.obj = obj;
		this.eqLabel = eqLabel;
		if (occs == null)
			this.occs = new ArrayList<Integer>();
		else
			this.occs = new ArrayList<Integer>(occs);
	}

	@Override
	protected String getString() {
		return "disch " + obj;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');

		// object
		obj.translate(buffer);

		// tactic
		if (eqLabel == null) {
			buffer.append(" (disch_tac ");
		}
		else {
			buffer.append(" (disch_eq_tac ");
			buffer.append('"');
			buffer.append(eqLabel);
			buffer.append('"');
			buffer.append(' ');
		}
		
		// occs
		buffer.append('[');
		int n = occs.size();
		for (int i = 0; i < n; i++) {
			buffer.append(occs.get(i));
			if (i < n - 1)
				buffer.append("; ");
		}
		buffer.append(']');
		
		buffer.append(')');
		buffer.append(')');
	}
}
