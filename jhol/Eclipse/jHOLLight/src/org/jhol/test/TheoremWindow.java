package org.jhol.test;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;

import javax.swing.BoxLayout;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;

/**
 * A window with theorems 
 */
@SuppressWarnings("serial")
public class TheoremWindow extends JDialog implements ActionListener {
	private CamlObjectList list;
	private JTextField termField;
	private JTextField nameField;
	
	private final CamlEnvironment caml;
	private final ExpressionBuilder builder;
	private final TheoremDatabase data;
	
	
	/**
	 * Constructor
	 */
	public TheoremWindow(CamlEnvironment caml, ExpressionBuilder builder, JFrame owner) {
		super(owner, false);
		this.caml = caml;
		this.builder = builder;
		this.data = new TheoremDatabase(caml);
		
		init();
	}
	
	
	/**
	 * Initialization
	 */
	private void init() {
		setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));
		
		list = new CamlObjectList();
		final JTable table = new JTable(list);

		table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		table.setColumnSelectionAllowed(false);
		table.setRowSelectionAllowed(false);
		
		table.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				if (e.getValueIsAdjusting())
					return;
				
				try {
					int index = table.getSelectedRow();
					if (index < 0)
						return;
					
					CamlObject obj = list.get(index);
					builder.insert(obj);
					
					table.getSelectionModel().clearSelection();
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		
		JScrollPane scroll = new JScrollPane(table);
		scroll.setPreferredSize(new Dimension(500, 300));
		
		add(scroll);
		
		// A field for entering new terms
		termField = new JTextField();
		termField.setActionCommand("term");
		termField.addActionListener(this);
		add(termField);
		
		// A field for entering names
		nameField = new JTextField();
		nameField.setActionCommand("name");
		nameField.addActionListener(this);
		add(nameField);
	}
	
	
	/**
	 * Action listener
	 */
	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == termField) {
			// Term
			String termString = termField.getText();
			String cmd = "`" + termString + "`";
			
			Term term;
			try {
				CamlObject obj = caml.execute(cmd, CamlType.TERM);
				if (!(obj instanceof Term))
					return;
				
				term = (Term) obj;
			}
			catch (Exception ex) {
				ex.printStackTrace();
				return;
			}
			
			list.clear();
			
			ArrayList<Theorem> ths = data.find(term);
			list.add(ths);
		}
		else if (e.getSource() == nameField){
			// Name
			list.clear();
			
			ArrayList<Theorem> ths = data.find(nameField.getText());
			list.add(ths);
		}
	}
}
