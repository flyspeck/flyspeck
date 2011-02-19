package edu.pitt.math.jhol.core.printer;

import java.util.ArrayList;

import edu.pitt.math.jhol.core.Term;

/**
 * A tree for printing terms
 */
public class TermPrinterTree {
	// The associated term
	protected final Term term;
	
	// Branches
	private final ArrayList<TermPrinterTree> branches;
	
	// Text (printed if it is not null)
	protected final String text;
	
	// If not null, then brackets are printed
	private String lbrack, rbrack;

	
	/**
	 * A base class for user-defined printers
	 */
	public abstract class Printer {
		public abstract String print(TermPrinterTree branch);
	}
	
	
	/**
	 * Constructor
	 */
	public TermPrinterTree(Term term, String text) {
		this.term = term;
		this.text = text;
		this.branches = new ArrayList<TermPrinterTree>();
	}
	
	
	/**
	 * Sets brackets
	 */
	public void setBrackets(String lbrack, String rbrack) {
		this.lbrack = lbrack;
		this.rbrack = rbrack;
	}
	
	
	/**
	 * Adds the branch
	 */
	public void addBranch(TermPrinterTree branch) {
		this.branches.add(branch);
	}
	
	
	/**
	 * Returns the associated term
	 */
	public Term getTerm() {
		return term;
	}
	
	
	/**
	 * Prints the tree using the given printer
	 */
	public String print(Printer printer) {
		StringBuilder str = new StringBuilder();
		if (lbrack != null)
			str.append(lbrack);
		
		str.append(printer.print(this));
		
		for (TermPrinterTree branch : branches) {
			str.append(branch.print(printer));
		}
		
		if (rbrack != null)
			str.append(rbrack);
		
		return str.toString();
	}
	
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		
		if (lbrack != null)
			str.append(lbrack);
		
		if (text != null) {
			str.append(text);
		}
		
		for (TermPrinterTree branch : branches) {
			str.append(branch);
		}
		
		if (rbrack != null)
			str.append(rbrack);
		
		return str.toString();
	}
}
