package edu.pitt.math.jhol.test;

import java.util.ArrayList;
import java.util.Collection;

import javax.swing.table.AbstractTableModel;


import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.core.printer.TermPrinter;
import edu.pitt.math.jhol.core.printer.TheoremPrinter;
import edu.pitt.math.jhol.core.printer.TypePrinter;

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
	 * Inserts the object at the given position
	 */
	public void add(int position, CamlObject obj) {
		if (!allowDuplicates) {
			if (objects.contains(obj))
				return;
		}
		
		objects.add(position, obj);
		fireTableDataChanged();
	}
	
	
	/**
	 * Adds the collection of objects into the list
	 */
	public void add(Collection<? extends CamlObject> objs) {
		int n = objects.size();
		
		for (CamlObject obj : objs) {
			if (!allowDuplicates) {
				if (objects.contains(obj))
					continue;
			}
			
			objects.add(obj);
		}
		
		fireTableRowsInserted(n, objects.size() - 1);
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
					return TermPrinter.print((Term) obj);
				}
				if (obj instanceof HOLType) {
					return "";
				}
				if (obj instanceof Theorem) {
					return TheoremPrinter.printSimple((Theorem) obj);
				}
				else if (obj != null) {
					return obj.toCommandString();
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
				else if (obj != null) {
					return obj.camlType();
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
