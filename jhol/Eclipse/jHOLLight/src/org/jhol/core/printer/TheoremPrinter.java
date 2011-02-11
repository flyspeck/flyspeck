package org.jhol.core.printer;

import org.jhol.core.Theorem;

/**
 * Prints a theorem
 */
public class TheoremPrinter {
	public static String printSimple(Theorem thm) {
		StringBuilder str = new StringBuilder();
		str.append("|- ");
		
		String concl = TermPrinter.simplePrint(thm.concl());
		str.append(concl);
		
		return str.toString();
	}
}
