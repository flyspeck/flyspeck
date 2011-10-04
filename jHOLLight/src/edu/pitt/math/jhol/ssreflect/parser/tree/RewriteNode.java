package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;


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
	// Special flag for -> and <- behavior
	private final boolean dischRewriteFlag;
	// Occ-switches
	private final ArrayList<Integer> occ;
	// Pattern (could be null)
	private final ObjectNode pattern;
	// Theorem
	private final ObjectNode theorem;
	
	
	/**
	 * Parameters of a rewrite operation
	 */
	public static class RewriteParameters {
		public boolean revFlag;
		public ArrayList<Integer> occ;
		public ObjectNode pattern;
		
		public boolean repeatFlag;
		public int rewrites;
		public boolean exactFlag;
		
		public boolean modifiedFlag;
		
		/**
		 * Constructor
		 */
		public RewriteParameters() {
			revFlag = false;
			occ = null;
			pattern = null;
			
			repeatFlag = false;
			rewrites = 1;
			exactFlag = true;
		}
	}
	
	
	/**
	 * Default constructor
	 */
	public RewriteNode(RewriteParameters params, ObjectNode theorem, 
				boolean dischRewriteFlag, boolean useHolRewrite) {
		assert(theorem != null);
		assert(params != null && params.rewrites > 0);
		
		this.revFlag = params.revFlag;
		this.occ = new ArrayList<Integer>();
		if (params.occ != null)
			this.occ.addAll(params.occ);
		this.pattern = params.pattern;
		
		this.theorem = theorem;

		this.rewrites = params.rewrites;
		this.repeatFlag = params.repeatFlag;
		this.exactFlag = params.exactFlag;

		this.dischRewriteFlag = dischRewriteFlag;
		this.useHolRewrite = useHolRewrite;
	}
	
	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder("rewrite ");
		if (useHolRewrite)
			str.append("<hol> ");
		if (revFlag)
			str.append('-');
		
		str.append(rewrites);
		if (exactFlag)
			str.append('!');
		else
			str.append('?');
		
		if (occ.size() > 0) {
			str.append('{');
			str.append(occ);
			str.append('}');
		}
		
		if (pattern != null) {
			str.append('[');
			str.append(pattern);
			str.append(']');
		}
				
		str.append(theorem);
		return str.toString();
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		if (!dischRewriteFlag)
			theorem.beginTranslation(buffer, context);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		if (!dischRewriteFlag)
			theorem.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		
		String beginRepeat = "";
		String endRepeat = "";
		
		// ->
		String name = "";
		if (dischRewriteFlag) {
			name = getUniqTheoremName();
			buffer.append("DISCH_THEN (fun " + name + " -> (");
		}
		
		// ? or !
		if (!exactFlag) {
			// ?
			int r = rewrites;
			if (repeatFlag)
				r = 10;
			
			beginRepeat = "repeat_tactic 0 " + r + " (";
			endRepeat = ")";
		}
		else {
			// !
			if (repeatFlag)
				beginRepeat = "repeat_tactic 1 9 (";
			else
				beginRepeat = "repeat_tactic " + rewrites + " 0 (";
			endRepeat = ")";
		}
		
		buffer.append(beginRepeat);
		
		// rewrite or rewr
		if (useHolRewrite) {
			buffer.append("ONCE_REWRITE_TAC[");
		}
		else {
			buffer.append("rewrite ");

			// occ-switch
			buffer.append('[');
			int n = occ.size();
			for (int i = 0; i < n; i++) {
				buffer.append(occ.get(i));
				if (i < n - 1)
					buffer.append("; ");
			}
			buffer.append("] ");
			
			// pattern
			buffer.append('[');
			if (pattern != null)
				pattern.translate(buffer);
			buffer.append("] (");
		}
		
		// -
		if (revFlag)
			buffer.append("GSYM ");
		
		// Theorem
		if (dischRewriteFlag) {
			buffer.append(name);
		}
		else {
			theorem.translate(buffer);
		}
		
		// rewrite or rewr
		if (useHolRewrite)
			buffer.append("]");
		else
			buffer.append(")");
		
		// ? or !
		buffer.append(endRepeat);
		
		// ->
		if (dischRewriteFlag) {
			buffer.append("))");
		}
		
		buffer.append(')');
	}
	
}
