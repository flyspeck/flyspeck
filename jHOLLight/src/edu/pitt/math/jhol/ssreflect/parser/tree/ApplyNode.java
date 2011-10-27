package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * apply
 */
public class ApplyNode extends TacticNode {
	// An object could be applied directly
	private ObjectNode obj;
	
	
	/**
	 * Constructor
	 */
	public ApplyNode(ObjectNode obj) {
		this.obj = obj;
	}
	
	
	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		
		if (obj == null) {
			buffer.append("DISCH_THEN apply_tac");
		}
		else {
			int type = obj.getType(context);
			if (type != ObjectNode.THEOREM && type != ObjectNode.UNKNOWN)
				throw new RuntimeException("Only a theorem could be applied");
			
			obj.translate(buffer, context);
			buffer.append(" apply_tac");
		}
		
		buffer.append(')');
	}
	
	@Override
	protected String getString() {
		return "apply";
	}


}
