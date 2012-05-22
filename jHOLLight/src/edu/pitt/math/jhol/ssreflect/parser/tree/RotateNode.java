package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * first [n] last
 */
public class RotateNode extends LeftAssociativeTacticNode {
	private int n;
	
	/**
	 * Default constructor
	 */
	public RotateNode(int n) {
		this.n = n;
	}
	
	@Override
	protected String getString() {
		return "rotate " + n;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		// This method should be never called
		throw new RuntimeException("RotateNode.translate()");
	}
	
	@Override
	public TacticNode transformTactic(TacticChainNode left) {
		TacticNode rot = new RawTactic("THENL_ROT (" + n + ")");
		return new BinaryNode(false, rot, left, null);
	}
	
}
