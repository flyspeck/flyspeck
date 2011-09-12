package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * rewrite -{3 2}x
 */
public class RewriteNode extends TacticNode {
	// If true, then the standard ONCE_REWRITE_TAC[th] is used
	private final boolean useHolRewrite;
	// Reverse rewriting flag
	private final boolean revFlag;
	// Theorem
	private final ObjectNode theorem;
	
	/**
	 * Default constructor
	 */
	public RewriteNode(ObjectNode theorem, boolean useHolRewrite, boolean revFlag) {
		assert(theorem != null);
		this.theorem = theorem;
		this.useHolRewrite = useHolRewrite;
		this.revFlag = revFlag;
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder("rewrite ");
		if (useHolRewrite)
			str.append("{hol} ");
		if (revFlag)
			str.append('-');
		str.append(theorem);
		
		return str.toString();
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		theorem.beginTranslation(buffer, context);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		theorem.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		
		if (useHolRewrite)
			buffer.append("ONCE_REWRITE_TAC[");
		else
			buffer.append("rewrite [] (");
		
		if (revFlag)
			buffer.append("GSYM ");
		theorem.translate(buffer);
		
		if (useHolRewrite)
			buffer.append("]");
		else
			buffer.append(")");
		
		buffer.append(')');
	}
	
}
