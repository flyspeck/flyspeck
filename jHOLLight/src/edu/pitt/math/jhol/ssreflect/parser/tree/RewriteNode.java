package edu.pitt.math.jhol.ssreflect.parser.tree;


/**
 * rewrite -{3 2}x
 */
public class RewriteNode extends TacticNode {
	// If true, then the standard ONCE_REWRITE_TAC[th] is used
	private final boolean useHolRewrite;
	// Reverse rewriting flag
	private final boolean revFlag;
	// If true then the tactic is repeated as many times as possible 
	// (at most 10 to prevent deadlocks)
	private final boolean repeatFlag;
	// The number of rewrites
	private final int rewrites;
	// If true then the number of rewrites indicates the number of exact rewrites
	private final boolean exactFlag;
	// Theorem
	private final ObjectNode theorem;
	
	/**
	 * Default constructor
	 */
	public RewriteNode(ObjectNode theorem, boolean useHolRewrite, 
				boolean revFlag, int rewrites, boolean repeatFlag, boolean exactFlag) {
		assert(theorem != null);
		assert(rewrites > 0);
		this.theorem = theorem;
		this.useHolRewrite = useHolRewrite;
		this.revFlag = revFlag;
		this.repeatFlag = repeatFlag;
		this.rewrites = rewrites;
		this.exactFlag = exactFlag;
	}
	
	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder("rewrite ");
		if (useHolRewrite)
			str.append("{hol} ");
		if (revFlag)
			str.append('-');
		
		str.append(rewrites);
		if (exactFlag)
			str.append('!');
		else
			str.append('?');
				
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
		
		String beginRepeat = "";
		String endRepeat = "";
		
		if (!exactFlag) {
			int r = rewrites;
			if (repeatFlag)
				r = 10;
			
			beginRepeat = "repeat_tactic 0 " + r + " (";
			endRepeat = ")";
		}
		else {
			if (repeatFlag)
				beginRepeat = "repeat_tactic 1 9 (";
			else
				beginRepeat = "repeat_tactic " + rewrites + " 0 (";
			endRepeat = ")";
		}
		
		buffer.append(beginRepeat);
		
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
		
		buffer.append(endRepeat);		
		buffer.append(')');
	}
	
}
