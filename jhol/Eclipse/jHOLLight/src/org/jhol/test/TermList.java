package org.jhol.test;

import java.util.ArrayList;

import javax.swing.table.AbstractTableModel;

import org.jhol.core.Term;
import org.jhol.core.printer.TermPrinter;
import org.jhol.core.printer.TypePrinter;

/**
 * List of terms
 * @author Alexey
 *
 */
@SuppressWarnings("serial")
public class TermList extends AbstractTableModel {
	// List of terms
	private final ArrayList<Term> terms;
	
	
	/**
	 * Default constructor
	 */
	public TermList() {
		terms = new ArrayList<Term>();
	}
	
	
	/**
	 * Adds the term into the list
	 * @param term
	 */
	public void addTerm(Term term) {
		// Do not add duplicates
		if (terms.contains(term))
			return;
		
		int n = terms.size();
		terms.add(term);
		fireTableRowsInserted(n, n);
	}
	
	
	/**
	 * Removes the term from the list
	 * @param term
	 */
	public void removeTerm(Term term) {
		int i = terms.indexOf(term);
		if (i < 0)
			return;
		
		terms.remove(i);
		fireTableRowsDeleted(i, i);
	}
	
	
	@Override
	public int getColumnCount() {
		// Term itself and its type
		return 2;
	}

	@Override
	public int getRowCount() {
		return terms.size();
	}

	@Override
	public Object getValueAt(int rowIndex, int columnIndex) {
		if (rowIndex >= terms.size())
			return null;
		
		Term term = terms.get(rowIndex);
		
		try {
			switch (columnIndex) {
			case 0:
				// The first column is the term itself
				return TermPrinter.simplePrint(term);
			case 1:
				// The second column is the type of the term
				return TypePrinter.printType(term.type());
			}
		}
		catch (Exception e) {
			e.printStackTrace();
			return null;
		}

		return null;
	}
	
	
	@Override
	public String getColumnName(int column) {
		switch (column) {
		case 0:
			return "Term";
		case 1:
			return "Type";
		}
		
		return null;
	}

}
