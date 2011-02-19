package edu.pitt.math.jhol.core.printer;

import edu.pitt.math.jhol.core.Theorem;

/**
 * Prints a theorem
 */
public class TheoremPrinter {
	public static TermPrinterTree printSimple(Theorem thm) {
		TermPrinterTree tree = new TermPrinterTree(null, null);
		
		if (thm.hyp())
			tree.addBranch(new TermPrinterTree(null, "A "));

		tree.addBranch(new TermPrinterTree(null, "|- "));
		
		TermPrinterTree concl = TermPrinter.print(thm.concl());
		tree.addBranch(concl);
		
		return tree;
	}
}
