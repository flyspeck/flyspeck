package edu.pitt.math.jhol.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.event.ActionEvent;

import javax.swing.AbstractCellEditor;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;


/**
 * A table of Caml objects
 */
@SuppressWarnings("serial")
public class CamlObjectTable extends JTable {
	/**
	 * Creates a table with the given data
	 */
	public CamlObjectTable(CamlObjectList data) {
		super(data);
		
		this.setDefaultRenderer(CamlObjectComponent.Element.class, new CamlObjectRenderer());
		this.setDefaultEditor(CamlObjectComponent.Element.class, new CamlObjectEditor());
	}

	
	/**
	 * Renderer for Caml objects
	 */
	static class CamlObjectRenderer extends CamlObjectComponent implements 
			TableCellRenderer {
		public CamlObjectRenderer() {
			super(true, false, false);
			setOpaque(true);
		}

		@Override
		public Component getTableCellRendererComponent(JTable table,
				Object value, boolean isSelected, boolean hasFocus, int row,
				int column) {

			if (!(value instanceof Element))
				return null;

			Element element = (Element) value;

			// Initialize properties
			setTextWidth(table.getColumnModel().getColumn(column).getWidth());
			float y = init(element.object);
			setSelection(element.level, element.index);

			if (isSelected) {
				setBackground(Color.LIGHT_GRAY);
			} else {
				setBackground(Color.WHITE);
			}

			if (table.getRowHeight(row) != (int) y) {
				table.setRowHeight(row, (int) y);
			}

			return this;
		}
	}
	
	
	
	/**
	 * Editor for Caml objects (manages selection)
	 */
	static class CamlObjectEditor extends AbstractCellEditor implements TableCellEditor {
		protected static final String EDIT = "edit";
		private CamlObjectComponent comp = new CamlObjectComponent(true, false, true);

		public CamlObjectEditor() {
		}

		public void actionPerformed(ActionEvent e) {
			if (EDIT.equals(e.getActionCommand())) {
//				comp.resetSelection();
//				fireEditingStopped();
			}
		}

		// Implement the one CellEditor method that AbstractCellEditor doesn't.
		public Object getCellEditorValue() {
			return comp.getElement();
		}

		// Implement the one method defined by TableCellEditor.
		public Component getTableCellEditorComponent(JTable table, Object value,
				boolean isSelected, int row, int column) {
			if (!(value instanceof CamlObjectComponent.Element))
				return null;

			CamlObjectComponent.Element element = (CamlObjectComponent.Element) value;
			
			comp.setTextWidth(table.getColumnModel().getColumn(column).getWidth());
			comp.init(element.object);
			comp.setSelection(element.level, element.index);
			
			return comp;
		}
	}


}
