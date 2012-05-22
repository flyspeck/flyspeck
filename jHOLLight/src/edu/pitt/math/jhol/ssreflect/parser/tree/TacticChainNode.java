package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * A chain of tactics
 */
public class TacticChainNode extends TacticNode {
	// A list of all tactics in the chain
	protected ArrayList<TacticNode> tactics = new ArrayList<TacticNode>();

	/**
	 * Default constructor
	 */
	public TacticChainNode() {
	}
	
	/**
	 * Constructs a chain with the given first tactic
	 */
	public TacticChainNode(TacticNode tac) {
		add(tac);
	}
	
	/**
	 * Copy constructor
	 */
	public TacticChainNode(TacticChainNode chain) {
		addChain(chain);
	}
	
	/**
	 * Adds a tactics to the chain
	 * @param tactic
	 */
	public void add(TacticNode tactic) {
		if (tactic == null)
			return;
		
		tactics.add(tactic);
	}
	
	/**
	 * Appends the given chain to this chain
	 */
	public void addChain(TacticChainNode chain) {
		if (chain == null)
			return;
		
		tactics.addAll(chain.tactics);
	}
	
	/**
	 * Returns the number of tactics in the chain
	 */
	public int size() {
		return tactics.size();
	}
	
	/**
	 * Returns true if the chain contains nothing or other empty chains
	 */
	public boolean isEmpty() {
		for (TacticNode tactic : tactics) {
			if (tactic instanceof TacticChainNode) {
				if (!((TacticChainNode) tactic).isEmpty())
					return false;
			}
			else {
				return false;
			}
		}
		
		return true;
	}
	
	/**
	 * Returns the i-th tactic in the chain
	 */
	public TacticNode get(int i) {
		return tactics.get(i);
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append('(');

		int n = size();
		for (int i = 0; i < n; i++) {
			TacticNode tac = tactics.get(i);
			str.append(tac);
			if (i < n - 1)
				str.append(" >>> ");
		}
		
		str.append(')');
		
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer) {
		int n = size();
		if (n == 0) {
			buffer.append("ALL_TAC");
			return;
		}
		
		// Transform all left associative tactics
		TacticChainNode left = new TacticChainNode();
		boolean transformFlag = false;
		
		for (int i = 0; i < n; i++) {
			TacticNode tac = tactics.get(i);
			
			if (tac instanceof LeftAssociativeTacticNode) {
				TacticNode newLeft = ((LeftAssociativeTacticNode) tac).transformTactic(left);
				left = new TacticChainNode(newLeft);
				transformFlag = true;
			}
			else {
				left.add(tac);
			}
		}
		
		// If there is a transformation then process the new chain 
		if (transformFlag) {
			left.translate(buffer);
			return;
		}
		
		// No transformations (no left associative tactics): continue the translation process
		boolean parFlag = n > 1;
		
		if (parFlag)
			buffer.append('(');

		for (int i = 0; i < n; i++) {
			tactics.get(i).translate(buffer);
			if (i < n - 1) {
				buffer.append(" THEN ");
			}
		}
		
		if (parFlag)
			buffer.append(')');
	}
}
