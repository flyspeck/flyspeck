package edu.pitt.math.jhol.core.printer;

import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;

/**
 * Returns printable trees for Caml objects
 */
public class Printer {
	/**
	 * Prints a term
	 */
	public static SelectionTree print(Term tm) {
		return TermPrinter.print(tm);
	}
	

	/**
	 * Prints a theorem
	 */
	public static SelectionTree print(Theorem th) {
		return TheoremPrinter.print(th);
	}
	
	
	/**
	 * Prints a HOL type
	 */
	public static SelectionTree print(HOLType type) {
		return TypePrinter.print(type);
	}
	
	
	/**
	 * Prints a generic Caml object
	 */
	public static SelectionTree print(CamlObject obj) {
		if (obj instanceof Term)
			return print((Term) obj);
		
		if (obj instanceof Theorem)
			return print((Theorem) obj);
		
		if (obj instanceof HOLType)
			return print((HOLType) obj);
		
		
		// Default
		SelectionTree tree = new SelectionTree(obj, obj.toString());
		return tree;
	}
}
