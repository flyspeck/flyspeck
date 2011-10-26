package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A node for a tactic
 */
public abstract class TacticNode extends Node {
	@Override
	public String getRevertCommand() {
		return "b()";
	}
	
	/**
	 * Returns true if the tactic is a set of parallel tactics
	 * @return
	 */
	public boolean isParallel() {
		return false;
	}
}
