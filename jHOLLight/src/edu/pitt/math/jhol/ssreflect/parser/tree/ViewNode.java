package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * move/x
 */
public class ViewNode extends TacticNode {
	// Object
	private final ObjectNode obj;
	
	/**
	 * Default constructor
	 */
	public ViewNode(ObjectNode obj) {
		assert(obj != null);
		this.obj = obj;
	}

	@Override
	protected String getString() {
		return "view " + obj;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		
		if (obj.isWildCard()) {
			// Translate a wild card directly
			obj.translate(buffer);
			buffer.append(" (thm_tac MP_TAC)");
		}
		else {
			buffer.append("DISCH_THEN (fun snd_th -> ");
			obj.translate(buffer);
			buffer.append(" (thm_tac (match_mp_then snd_th MP_TAC))");
			buffer.append(')');
		}
		
		buffer.append(')');
	}
}
