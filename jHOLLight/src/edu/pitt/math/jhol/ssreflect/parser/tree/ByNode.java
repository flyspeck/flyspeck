package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * by chain
 */
public class ByNode extends LeftAssociativeTacticNode {
	private TacticChainNode chain;
	
	/**
	 * Default constructor
	 */
	public ByNode(TacticChainNode chain) {
		assert (chain != null);
		this.chain = chain;
	}
	
	@Override
	protected String getString() {
		return "by " + chain;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		// This method should be never called
		throw new RuntimeException("ByNode.translate()");
	}
	
	@Override
	public TacticNode transformTactic(TacticChainNode left) {
		chain.add(new RawTactic("done_tac"));
		left.addChain(chain);
		return left;
	}
	
}
