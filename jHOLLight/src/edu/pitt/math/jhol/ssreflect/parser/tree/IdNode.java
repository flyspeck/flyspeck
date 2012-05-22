package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * An object defined by an identifier
 */
public class IdNode extends ObjectNode {
	// Constant Id
	public static final IdNode TMP_ID = new IdNode("_tmp_");

	// The identifier
	private final String id;

	// Indicates if the object should be cleared from the assumption list
	private boolean clearFlag;

	
	/**
	 * Default constructor
	 */
	public IdNode(String id) {
		assert(id != null);
		this.id = id;
	}
	
	/**
	 * clearFlag getter
	 */
	public boolean getClearFlag() {
		return clearFlag;
	}
	
	/**
	 * clearFlag setter
	 */
	public void setClearFlag(boolean flag) {
		this.clearFlag = flag;
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
	protected void translate(StringBuffer buffer) {
		buffer.append("(use_arg_then \"" + id + "\")");
	}
	
	
	@Override
	protected int getType() {
		return UNKNOWN;
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
