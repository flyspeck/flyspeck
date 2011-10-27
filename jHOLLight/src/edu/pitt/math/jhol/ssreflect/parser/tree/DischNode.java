package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * move: x
 */
public class DischNode extends TacticNode {
	// The object which is discharged
	private final ObjectNode obj;
	
	/**
	 * Default constructor
	 */
	public DischNode(ObjectNode obj) {
		assert(obj != null);
		this.obj = obj;
	}

	@Override
	protected String getString() {
		return "disch " + obj;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		
		int type = obj.getType(context);
		if (type == ObjectNode.TERM) {
			// term: SPEC_TAC
			StringBuffer varBuffer = new StringBuffer();
			obj.translate(varBuffer, context);
			buffer.append("SPEC_TAC (");
			buffer.append(varBuffer);
			buffer.append(',');
			buffer.append(varBuffer);
			buffer.append(')');
		}
		else {
			// theorem: MP_TAC
			obj.translate(buffer, context);
			buffer.append("MP_TAC");
		}
		
		buffer.append(')');
	}
}
