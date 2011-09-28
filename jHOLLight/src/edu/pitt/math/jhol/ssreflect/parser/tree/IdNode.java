package edu.pitt.math.jhol.ssreflect.parser.tree;

import edu.pitt.math.jhol.core.Term;

/**
 * An object defined by an identifier
 */
public class IdNode extends ObjectNode {
	// The identifier
	private final String id;
	
	// Type is defined by the context
	private int type;
	
	// Translation string is computed in the beginTranslation() method
	private String translationString;
	// If true, then this node corresponds to an assumption
	private boolean assumptionFlag;
	
	// Constant Id
	public static final IdNode TMP_ID = new IdNode("_tmp_");
	
	/**
	 * Default constructor
	 */
	public IdNode(String id) {
		assert(id != null);
		this.id = id;
	}
	
	/**
	 * id getter
	 */
	public String getId() {
		return id;
	}

	@Override
	protected String getString() {
		return id;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		// Set default values first
		type = THEOREM;
		translationString = id;
		assumptionFlag = false;

		// Free variables have priority
		Term var = context.getFreeVariable(id);
		
		if (var != null) {
			// Free variable
			translationString = "(" + var.makeCamlCommand() + ")";
			type = TERM;
		}
		else {
			assumptionFlag = context.isAssumptionName(id);
			if (assumptionFlag) {
				// Generate name
				translationString = getUniqTheoremName();
				// Modify the buffer
				buffer.append("USE_THEN \"" + id + "\" (fun " + translationString + " -> ");
			}
		}
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		if (assumptionFlag) {
			buffer.append(")");
		}
	}

	@Override
	protected void translate(StringBuffer buffer) {
		assert(translationString != null);
		buffer.append(translationString);
	}

	@Override
	protected int getType() {
		return type;
	}

	/**
	 * Returns true if the object represents an assumption
	 */
	protected boolean isAssumption() {
		return assumptionFlag;
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
