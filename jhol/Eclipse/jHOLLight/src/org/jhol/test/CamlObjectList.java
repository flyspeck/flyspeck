package org.jhol.test;

import java.util.ArrayList;

import javax.swing.table.AbstractTableModel;

import org.jhol.caml.CamlObject;
import org.jhol.core.HOLType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;
import org.jhol.core.printer.TermPrinter;
import org.jhol.core.printer.TheoremPrinter;
import org.jhol.core.printer.TypePrinter;

/**
 * A table model for (mixed) Caml objects
 * @author Alexey
 *
 */
@SuppressWarnings("serial")
public class CamlObjectList extends AbstractTableModel {
	// List of objects
	private final ArrayList<CamlObject> objects;
	
	// If true then duplicates in the list are allowed
	private boolean allowDuplicates;
	
	
	/**
	 * Constructor
	 */
	public CamlObjectList(boolean allowDuplicates) {
		this.allowDuplicates = allowDuplicates;
		this.objects = new ArrayList<CamlObject>();
	}
	
	public CamlObjectList() {
		this(false);
	}
	
	
	/**
	 * Returns the number of objects in the list
	 */
	public int size() {
		return objects.size();
	}
	
	
	/**
	 * Returns the i-th object in the list
	 * @param index
	 * @return
	 */
	public CamlObject get(int i) {
		return objects.get(i);
	}
	
	
	/**
	 * Adds the object into the list
	 * @param term
	 */
	public void add(CamlObject obj) {
		if (!allowDuplicates) {
			// Do not add duplicates
			if (objects.contains(obj))
				return;
		}
		
		int n = objects.size();
		objects.add(obj);
		fireTableRowsInserted(n, n);
	}
	
	
	/**
	 * Removes the object from the list
	 * @param term
	 */
	public void remove(CamlObject obj) {
		int i = objects.indexOf(obj);
		if (i < 0)
			return;
		
		objects.remove(i);
		fireTableRowsDeleted(i, i);
	}
	
	
	/**
	 * Clears the list
	 */
	public void clear() {
		objects.clear();
		fireTableDataChanged();
	}
	
	
	@Override
	public int getColumnCount() {
		// Term itself and its type
		return 2;
	}

	@Override
	public int getRowCount() {
		return objects.size();
	}

	@Override
	public Object getValueAt(int rowIndex, int columnIndex) {
		if (rowIndex >= objects.size())
			return null;
		
		CamlObject obj = objects.get(rowIndex);
		
		try {
			switch (columnIndex) {
			// Column 1
			case 0:
				if (obj instanceof Term) {
					return TermPrinter.simplePrint((Term) obj);
				}
				if (obj instanceof HOLType) {
					return "";
				}
				if (obj instanceof Theorem) {
					return TheoremPrinter.printSimple((Theorem) obj);
				}
				break;

			// Column 2
			case 1:
				if (obj instanceof Term) {
					return TypePrinter.printType(((Term) obj).type());
				}
				if (obj instanceof HOLType) {
					return TypePrinter.printType((HOLType) obj);
				}
				if (obj instanceof Theorem) {
					String name = ((Theorem) obj).name();
					return name != null ? name : "%TMP_THEOREM%";
				}
				break;
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
			return "Concl/Term";
		case 1:
			return "Name/Type";
		}
		
		return null;
	}

}
