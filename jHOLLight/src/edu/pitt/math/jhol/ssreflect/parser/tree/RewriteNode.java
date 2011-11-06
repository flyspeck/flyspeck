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
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		
		if (dischRewriteFlag) {
			// ->
			buffer.append("DISCH_THEN");
		}
		else {
			theorem.translate(buffer, context);
		}
		
		buffer.append('(');
		// -
		if (revFlag) {
			buffer.append("GSYM_THEN (");
		}
		
		// rewrite or rewr
		if (useHolRewrite) {
			buffer.append("fun th -> ONCE_REWRITE_TAC[th]");
		}
		else {
			buffer.append("new_rewrite ");

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
				pattern.translate(buffer, context);
			buffer.append("]");
		}
		
		// -
		if (revFlag)
			buffer.append(")");
		
		buffer.append(')');
		buffer.append(')');
	}
	
}
