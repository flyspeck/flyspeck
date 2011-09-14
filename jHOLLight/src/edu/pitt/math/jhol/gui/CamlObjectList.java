package edu.pitt.math.jhol.gui;

import java.util.ArrayList;
import java.util.Collection;

import javax.swing.table.AbstractTableModel;


import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.core.printer.TypePrinter;

/**
 * A table model for (mixed) Caml objects
 */
@SuppressWarnings("serial")
public class CamlObjectList extends AbstractTableModel {

	// List of objects
	private final ArrayList<CamlObjectComponent.Element> objects;
	
	// If true then duplicates in the list are allowed
	private final boolean allowDuplicates;
	
	// If true then only one column is used
	private final boolean oneColumn;
	
	// Names of columns
	private String firstColumnName = "Concl/Term";
	private String secondColumnName = "Name/Type";
	
	
	/**
	 * Constructor
	 */
	public CamlObjectList(boolean oneColumn, boolean allowDuplicates) {
		this.oneColumn = oneColumn;
		this.allowDuplicates = allowDuplicates;
		this.objects = new ArrayList<CamlObjectComponent.Element>();
	}
	
	public CamlObjectList() {
		this(false, false);
	}
	
	
	/**
	 * Sets the names of columns
	 */
	public void setColumnNames(String firstName, String secondName) {
		if (firstName == null)
			firstName = "";
		if (secondName == null)
			secondName = "";
		
		this.firstColumnName = firstName;
		this.secondColumnName = secondName;
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
		return objects.get(i).object;
	}
	
	
	/**
	 * Adds the object into the list
	 * @param term
	 */
	public void add(CamlObject obj) {
		if (obj == null) {
			throw new RuntimeException("CamlObjectList: null objects are not allowed");
		}
		
		CamlObjectComponent.Element e = new CamlObjectComponent.Element(obj);
		
		if (!allowDuplicates) {
			// Do not add duplicates
			if (objects.contains(e))
				return;
		}
		
		int n = objects.size();
		objects.add(e);
		fireTableRowsInserted(n, n);
	}
	
	
	/**
	 * Inserts the object at the given position
	 */
	public void add(int position, CamlObject obj) {
		if (position < 0)
			position = 0;
		
		if (position > objects.size())
			position = objects.size();
		
		if (obj == null) {
			throw new RuntimeException("CamlObjectList: null objects are not allowed");
		}
		
		CamlObjectComponent.Element e = new CamlObjectComponent.Element(obj);
		
		if (!allowDuplicates) {
			if (objects.contains(e))
				return;
		}
		
		objects.add(position, e);
		fireTableDataChanged();
	}
	
	
	/**
	 * Adds the collection of objects into the list
	 */
	public void add(Collection<? extends CamlObject> objs) {
		int n = objects.size();
		
		for (CamlObject obj : objs) {
			CamlObjectComponent.Element e = new CamlObjectComponent.Element(obj);
			
			if (!allowDuplicates) {
				if (objects.contains(e))
					continue;
			}
			
			objects.add(e);
		}
		
		fireTableRowsInserted(n, objects.size() - 1);
	}
	
	
	/**
	 * Removes the object from the list
	 * @param term
	 */
	public void remove(CamlObject obj) {
		CamlObjectComponent.Element e = new CamlObjectComponent.Element(obj);
		
		int i = objects.indexOf(e);
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
		return oneColumn ? 1 : 2;
	}

	@Override
	public int getRowCount() {
		return objects.size();
	}
	
	
	@Override
	public boolean isCellEditable(int rowIndex, int columnIndex) {
		if (columnIndex == 0)
			return true;
		
		return false;
	}
	
	
	@Override
	public Class<?> getColumnClass(int columnIndex) {
		switch (columnIndex) {
		case 0:
			return CamlObjectComponent.Element.class;
		}
		
		return Object.class;
	}
	
	
	@Override
	public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
		if (!(aValue instanceof CamlObjectComponent.Element))
			return;
		
		if (aValue == null)
			return;
		
		objects.set(rowIndex, (CamlObjectComponent.Element) aValue);
	}
	

	@Override
	public Object getValueAt(int rowIndex, int columnIndex) {
		if (rowIndex >= objects.size())
			return null;
		
		CamlObjectComponent.Element e = objects.get(rowIndex);
		
		try {
			switch (columnIndex) {
			// Column 1
			case 0:
				return e;

			// Column 2
			case 1:
				CamlObject obj = e.object;
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
		catch (Exception ex) {
			ex.printStackTrace();
			return null;
		}

		return null;
	}
	
	
	@Override
	public String getColumnName(int column) {
		switch (column) {
		case 0:
			return firstColumnName;
		case 1:
			return secondColumnName;
		}
		
		return null;
	}

}
