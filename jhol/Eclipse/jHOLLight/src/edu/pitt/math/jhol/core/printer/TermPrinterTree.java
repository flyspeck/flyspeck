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
	 * Describes a subterm
	 */
	public static class Subterm {
		public final Term tm;
		public final int start;
		public final int end;
		
		public Subterm(Term tm, int start, int end) {
			this.tm = tm;
			this.start = start;
			this.end = end;
		}
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
	
	
	/**
	 * Returns the term associated with the character at the given position
	 * and at the given depth level
	 */
	public Subterm getSubterm(int pos, int level) {
		int start = 0;
		int end = this.toString().length();
		Subterm def = new Subterm(term, start, end);
		
		int dpos = 0;
		
		if (level <= 0)
			return def;
		
		if (lbrack != null) {
			if (pos < lbrack.length())
				return def;
			
			pos -= 1;
			dpos += 1;
		}
		
		if (text != null) {
			if (pos < text.length())
				return new Subterm(term, start, end);
			
			pos -= text.length();
			dpos += text.length();
		}
		
		for (TermPrinterTree branch : branches) {
			String str = branch.toString();
			if (pos < str.length()) {
				Subterm tm = branch.getSubterm(pos, level - 1);
				if (tm.tm == null)
					return def;
				else
					return new Subterm(tm.tm, tm.start + dpos, tm.end + dpos);
			}
			
			pos -= str.length();
			dpos += str.length();
		}
		
		return def;
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
