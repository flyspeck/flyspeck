package edu.pitt.math.jhol.core.printer;

import edu.pitt.math.jhol.core.Theorem;

/**
 * Prints a theorem
 */
public class TheoremPrinter {
	public static String printSimple(Theorem thm) {
		StringBuilder str = new StringBuilder();
		
		if (thm.hyp())
			str.append("A ");
		
		str.append("|- ");
		
		String concl = TermPrinter.print(thm.concl());
		str.append(concl);
		
		return str.toString();
	}
}
