package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Represents a tactic which is left associative in a chain of tactics
 */
public abstract class LeftAssociativeTacticNode extends TacticNode {
	/**
	 * Creates a new tactic which is right associative in a chain of tactics.
	 * The result of the transformation must not be a left associative tactic.
	 */
	public abstract TacticNode transformTactic(TacticChainNode left);
}
