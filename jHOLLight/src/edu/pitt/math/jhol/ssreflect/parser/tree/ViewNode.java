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
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		obj.beginTranslation(buffer, context);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		obj.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		String name = getUniqTheoremName();
		buffer.append('(');
		buffer.append("DISCH_THEN (MP_TAC o (fun " + name + " -> ");
		
		// TODO: find a better solution 
		if (obj.isWildCard()) {
			obj.setWildCardInterpretation(name);
			obj.translate(buffer);
			obj.setWildCardInterpretation(null);
		}
		else {
			buffer.append("MATCH_MP ");
			obj.translate(buffer);
			buffer.append(' ');
			buffer.append(name);
		}

		buffer.append("))");
		buffer.append(')');
	}
}
