package org.jhol.core.printer;

import org.jhol.core.HOLType;
import org.jhol.core.Pair;
import org.jhol.core.Term;
import static org.jhol.core.Term.*;

/**
 * Prints a term
 */
public class TermPrinter {
	public static String simplePrint(Term t) {
		if (is_var(t)) {
			Pair<String, HOLType> p = dest_var(t);
			return p.getFirst();
		}
		
		if (is_const(t)) {
			Pair<String, HOLType> p = dest_const(t);
			return "(" + p.getFirst() + ")";
		}
		
		if (is_comb(t)) {
			Pair<Term, Term> p = dest_comb(t);
			Term t1 = p.getFirst();
			Term t2 = p.getSecond();
			
			String s1 = simplePrint(p.getFirst());
			String s2 = simplePrint(p.getSecond());
			
			if (is_abs(t1))
				s1 = "(" + s1 + ")";
			
			if (is_comb(t2) || is_abs(t2))
				s2 = "(" + s2 + ")";
			
			return s1 + " " + s2;
		}
		
		if (is_abs(t)) {
			Pair<Term, Term> p = dest_abs(t);
			String s1 = simplePrint(p.getFirst());
			String s2 = simplePrint(p.getSecond());
			
			return "\\" + s1 + ". " + s2;
		}
		
		throw new Error("Impossible");
	}
}
