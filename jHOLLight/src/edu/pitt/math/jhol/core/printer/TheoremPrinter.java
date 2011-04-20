package edu.pitt.math.jhol.core.printer;

import edu.pitt.math.jhol.core.Theorem;

/**
 * Prints a theorem
 */
public class TheoremPrinter {
	public static SelectionTree printSimple(Theorem thm) {
		SelectionTree tree = new SelectionTree(null, null);
		
		if (thm.hyp())
			tree.addBranch(new SelectionTree(null, "A "));

		tree.addBranch(new SelectionTree(null, "|- "));
		
		SelectionTree concl = TermPrinter.print(thm.concl());
		tree.addBranch(concl);
		
		return tree;
	}
	
	
	/**
	 * Prints a theorem
	 */
	public static SelectionTree print(Theorem th) {
		SelectionTree tree = new SelectionTree(th, null);
		
		if (th.hyp()) {
			tree.addBranch(new SelectionTree(th, "A "));
		}
		
		tree.addBranch(new SelectionTree(null, "|- "));

		SelectionTree concl = TermPrinter.print(th.concl());
		tree.addBranch(concl);
		
		return tree;
	}
}
