package edu.pitt.math.jhol.ssreflect.parser.tree;

import edu.pitt.math.jhol.ssreflect.parser.tree.RewriteNode.RewriteParameters;

/**
 * 'do' expression
 */
public class RepeatNode extends TacticNode {
	// If true then the tactic is repeated as many times as possible 
	// (at most 10 to prevent deadlocks)
	private final boolean repeatFlag;
	// The number of iterations;
	private final int iterations;
	// If true then the number of rewrites indicates the number of exact rewrites
	private final boolean exactFlag;
	
	// A list of tactics to repeat (only one of them is performed at each iteration step)
	private final TacticParallelNode tactics;

	/**
	 * Constructor
	 */
	public RepeatNode(TacticParallelNode tactics, int iterations, boolean repeatFlag, boolean exactFlag) {
		assert(tactics != null && tactics.size() > 0);
		assert(iterations >= 0);
		
		this.tactics = tactics;
		this.iterations = iterations;
		this.repeatFlag = repeatFlag;
		this.exactFlag = exactFlag;
	}
	
	/**
	 * Constructor for a rewrite expression
	 */
	public RepeatNode(RewriteNode r, RewriteParameters params) {
		this(new TacticParallelNode(new TacticChainNode(r)), params.rewrites, params.repeatFlag, params.exactFlag);
	}

	@Override
	protected String getString() {
		StringBuffer str = new StringBuffer("do ");
		
		str.append(iterations);
		if (exactFlag)
			str.append('!');
		else
			str.append('?');
		
		str.append(tactics);
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer) {
		String beginRepeat;
		String endRepeat;
		
		if (!repeatFlag && exactFlag && iterations == 1) {
			beginRepeat = endRepeat = "";
		}
		else {
			// ? or !
			if (!exactFlag) {
				// ?
				int r = iterations;
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
					beginRepeat = "repeat_tactic " + iterations + " 0 (";
				endRepeat = ")";
			}
		}

		buffer.append('(');
		
		buffer.append(beginRepeat);
		if (tactics.size() > 1) {
			buffer.append("FIRST ");
		}
		
		// If tactics.size() > 1 then square brackets will be added automatically
		tactics.translate(buffer);
		
		buffer.append(endRepeat);
		buffer.append(')');
	}

}
