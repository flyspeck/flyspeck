package org.jhol.test;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTable;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.HOLType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;

/**
 * A class for building new theorems and terms
 */
@SuppressWarnings("serial")
public class ExpressionBuilder extends JPanel implements ActionListener {
	private CamlObject lhs, rhs;
	
	private final CamlEnvironment caml;
	
	// The result of the expression evaluation is stored here
	private final CamlObjectList result;
	
	// Textual representation of the expression
	private final JLabel exprText;
	
	// Clears the expression
	private final JButton clearButton;
	
	
	/**
	 * Constructor
	 */
	public ExpressionBuilder(final TestGUI mainFrame, CamlEnvironment caml) {
		this.caml = caml;
		
		// Create visual components
		result = new CamlObjectList();
		exprText = new JLabel();
		exprText.setBackground(Color.WHITE);
		
		clearButton = new JButton("Clear");
		clearButton.setActionCommand("clear");
		clearButton.addActionListener(this);
		
		// Add the components into the panel
		this.setLayout(new BoxLayout(this, BoxLayout.PAGE_AXIS));
		
		final JTable resultTable = new JTable(result);
		resultTable.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				int i = resultTable.getSelectedRow();
				if (i < 0)
					return;
				
				mainFrame.getTerms().add(result.get(i));
			}
		});
		
		JScrollPane scroll = new JScrollPane(resultTable);
		scroll.setPreferredSize(new Dimension(500, 100));
		
		exprText.setPreferredSize(new Dimension(500, 50));
		
		JSplitPane splitter = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
		splitter.setLeftComponent(scroll);
		splitter.setRightComponent(exprText);

		this.add(splitter);
		this.add(clearButton);
	}
	

	/**
	 * Adds the object to the expression 
	 * @return true if the object has been accepted
	 */
	public boolean insert(CamlObject obj) throws Exception {
		if (lhs == null) {
			if (rhs == null) {
				// lhs == null && rhs == null
				// Accept either terms, theorems, types as rhs, or functions as lhs
				if (obj instanceof Term || obj instanceof Theorem || obj instanceof HOLType) {
					rhs = obj;
					update();
					return true;
				}
				else {
					CamlType type = obj.camlType();
					if (type.numberOfArguments() > 0) {
						lhs = obj;
						update();
						return true;
					}
					
					return false;
				}
			}
			else {
				// lhs == null && rhs != null
				// Accept functions with the fixed type of the last argument
				int nargs = obj.camlType().numberOfArguments();
				if (nargs == 0)
					return false;
				
				CamlType lastArgType = obj.camlType().getArgType(nargs - 1);
				if (!lastArgType.equals(rhs.camlType()))
					return false;
				
				lhs = obj;
				update();
				return true;
			}
		}
		else {
			// lhs != null
			// Accept the next function argument
			CamlType argType = lhs.camlType().getArgType(0);
			if (argType == null)
				throw new Exception("Bad type: a function type is expected, lhs = " + lhs);
			
			if (!argType.equals(obj.camlType()))
				return false;
			
			lhs = lhs.apply(obj);
			update();
			return true;
		}
	}
	
	
	/**
	 * Returns the (partially) constructed expression
	 * @return
	 */
	private String getCommand() {
		String lhsStr = "";
		String rhsStr = "";
		int args = 0;
		
		if (lhs != null) {
			lhsStr = lhs.toCommandString();
			args = lhs.camlType().numberOfArguments();
		}
		
		if (rhs != null) {
			args -= 1;
			rhsStr = rhs.toCommandString();
			
			if (rhs instanceof CamlObject.CamlApplication || rhs instanceof Theorem.TempTheorem)
				rhsStr = "(" + rhsStr + ")";
		}

		for (int i = 0; i < args; i++) {
			lhsStr += " (...)";
		}

		return lhsStr + " " + rhsStr;
	}
	
	
	/**
	 * Updates the component
	 */
	private void update() throws Exception {
		if (lhs != null) {
			int nargs = lhs.camlType().numberOfArguments();
			
			if (nargs == 0) {
				if (rhs != null)
					throw new Exception("Unexpected number of arguments for lhs = " + lhs);
				
				// Evaluate the expression
				rhs = lhs.eval(caml);
				lhs = null;
			}
			else if (nargs == 1 && rhs != null) {
				// Apply the lhs to the rhs
				rhs = lhs.apply(rhs);
				lhs = null;
				
				// Evaluate the expression
				rhs = rhs.eval(caml);
			}
		}
		
		// Update the visual components
		result.clear();
		
		if (rhs != null)
			result.add(rhs);

		exprText.setText(getCommand());
	}


	@Override
	public void actionPerformed(ActionEvent e) {
		String cmd = e.getActionCommand().intern();
		
		// Clear
		if (cmd == "clear") {
			lhs = rhs = null;
			try {
				update();
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		}
	}
}
