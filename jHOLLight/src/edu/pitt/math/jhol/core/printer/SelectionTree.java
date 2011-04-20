package edu.pitt.math.jhol.core.printer;

import java.util.ArrayList;

import edu.pitt.math.jhol.caml.CamlObject;

/**
 * A tree for printing expression and for selecting subelements
 */
public class SelectionTree {
	// The associated element
	protected final CamlObject element;
	
	// Branches
	private final ArrayList<SelectionTree> branches;
	
	// Text (printed if it is not null)
	protected final String text;
	
	// If not null, then brackets are printed
	private String lbrack, rbrack;

	
	/**
	 * Describes a subelement
	 */
	public static class Subelement {
		public final CamlObject element;
		public final int level;
		public final int start;
		public final int end;
		
		public Subelement(CamlObject element, int level, int start, int end) {
			this.element = element;
			this.level = level;
			this.start = start;
			this.end = end;
		}
	}
	
	
	/**
	 * Constructor
	 */
	public SelectionTree(CamlObject element, String text) {
		this.element = element;
		this.text = text;
		this.branches = new ArrayList<SelectionTree>();
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
	public void addBranch(SelectionTree branch) {
		this.branches.add(branch);
	}
	
	
	/**
	 * Prints the tree using the given printer
	 */
/*	public String print(Printer printer) {
		StringBuilder str = new StringBuilder();
		if (lbrack != null)
			str.append(lbrack);
		
		str.append(printer.print(this));
		
		for (SelectionTree branch : branches) {
			str.append(branch.print(printer));
		}
		
		if (rbrack != null)
			str.append(rbrack);
		
		return str.toString();
	}
*/	
	
	/**
	 * Returns the term associated with the character at the given position
	 * and at the given depth level
	 */
	public Subelement getSubelement(int pos, int maxLevel) {
		return getSubelement0(pos, 0, maxLevel);
	}
	
	
	private Subelement getSubelement0(int pos, int level, int maxLevel) {
		int start = 0;
		int end = this.toString().length();
		Subelement def = new Subelement(element, level, start, end);
		
		int dpos = 0;
		
		if (level >= maxLevel)
			return def;
		
		if (lbrack != null) {
			if (pos < lbrack.length())
				return def;
			
			pos -= 1;
			dpos += 1;
		}
		
		if (text != null) {
			if (pos < text.length())
				return def;
			
			pos -= text.length();
			dpos += text.length();
		}
		
		for (SelectionTree branch : branches) {
			String str = branch.toString();
			if (pos < str.length()) {
				Subelement e = branch.getSubelement0(pos, level + 1, maxLevel);
				if (e.element == null)
					return def;
				else
					return new Subelement(e.element, e.level, e.start + dpos, e.end + dpos);
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
		
		for (SelectionTree branch : branches) {
			str.append(branch);
		}
		
		if (rbrack != null)
			str.append(rbrack);
		
		return str.toString();
	}
}
