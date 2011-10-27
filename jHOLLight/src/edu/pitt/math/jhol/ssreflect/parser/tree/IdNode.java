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

	// Indicates if the object should be cleared from the assumption list
	public boolean clearFlag;

	
	// Constant Id
	public static final IdNode TMP_ID = new IdNode("_tmp_");
	
	/**
	 * Default constructor
	 */
	public IdNode(String id) {
		assert(id != null);
		this.id = id;
		this.type = -1;
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
	protected void translate(StringBuffer buffer, GoalContext context) {
		getType(context);
		assert(translationString != null);
		
		
		buffer.append(translationString);
	}
	
	
	@Override
	protected int getType(GoalContext context) {
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
				translationString = "(USE_THEN \"" + id + "\")";
			}
			else {
				translationString = "(USE_THM_THEN " + id + ")";
			}
		}
		
		return type;
	}

	/**
	 * Returns true if the object represents an assumption
	 */
	// FIXME: this function must be called after getType() 
	protected boolean isAssumption() {
		assert(type >= 0);
		return assumptionFlag;
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
