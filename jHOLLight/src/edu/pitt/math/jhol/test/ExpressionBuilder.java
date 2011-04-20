package edu.pitt.math.jhol.test;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTable;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlList;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;

/**
 * A class for building new theorems and terms
 */
@SuppressWarnings("serial")
public class ExpressionBuilder extends JPanel implements ActionListener {
	private CamlObject lhs, rhs;
	
	// Objects for a list
	private ArrayList<CamlObject> listObjects;
	
	private final CamlEnvironment caml;
	
	// The result of the expression evaluation is stored here
	private final CamlObjectList result;
	
	// Textual representation of the expression
	private final JLabel exprText;
	
	// Clears the expression
	private final JButton clearButton;
	
	// For updating the goal state
	private GoalstateWindow goalstateWindow;
	
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
	 * Sets the GoalstateWindow
	 * @param win
	 */
	public void setGoalstateWindow(GoalstateWindow win) {
		this.goalstateWindow = win;
	}
	

	/**
	 * Adds the object to the expression 
	 * @return true if the object has been accepted
	 */
	public boolean insert(CamlObject obj) throws Exception {
		if (obj == null) {
			// Special object
			if (listObjects != null) {
				CamlType elType = listObjects.get(0).camlType();
				// Close the list
				obj = new CamlList(elType, listObjects);
			}
			else {
				if (lhs != null) {
					CamlType argType = lhs.camlType().getArgType(0);
					if (argType != null && argType instanceof CamlType.ListType) {
						CamlType.ListType listType = (CamlType.ListType) argType;
						obj = new CamlList(listType.getElementType());
					}
					else {
						return false;
					}
				}
				else {
					return false;
				}
			}
		}
		
		if (lhs == null) {
			if (rhs == null) {
				// lhs == null && rhs == null
				// Accept either terms, theorems, types as rhs, or functions as lhs
				if (obj instanceof Term || obj instanceof Theorem || obj instanceof HOLType) {
					update(lhs, obj);
					return true;
				}
				else {
					CamlType type = obj.camlType();
					if (type.numberOfArguments() > 0 || type.equals(CamlType.TACTIC)) {
						update(obj, rhs);
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
				
				update(obj, rhs);
				return true;
			}
		}
		else {
			// lhs != null
			// Accept the next function argument
			CamlType argType = lhs.camlType().getArgType(0);
			if (argType == null)
				throw new Exception("Bad type: a function type is expected, lhs = " + lhs);
			
			if (!argType.equals(obj.camlType())) {
				// Special case for lists
				if (argType instanceof CamlType.ListType) {
					CamlType.ListType listType = (CamlType.ListType) argType;
					
					if (!listType.getElementType().equals(obj.camlType()))
						return false;
					
					if (listObjects == null)
						listObjects = new ArrayList<CamlObject>();
					
					listObjects.add(obj);
					update(lhs, rhs);
					return true;
				}
				
				return false;
			}
			else {
				listObjects = null;
			}
			
			update(lhs.apply(obj), rhs);
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
			lhsStr += " ";
			CamlType argType = lhs.camlType().getArgType(i);
			if (argType instanceof CamlType.ListType) {
				if (i == 0 && listObjects != null) {
					lhsStr += "[";
					for (CamlObject obj : listObjects) {
						lhsStr += obj.toCommandString();
						lhsStr += "; ";
					}
					lhsStr += "...]";
				}
				else {
					lhsStr += "[...]";
				}
			}
			else {
				lhsStr += "(...)";
			}
		}

		return lhsStr + " " + rhsStr;
	}
	
	
	private void evalTactic(CamlObject tac) throws Exception {
		String cmd = "(hd o e) (" + tac.makeCamlCommand() + ")";
		Goalstate newState = (Goalstate) caml.execute(cmd, CamlType.GOAL_STATE);
		
		if (newState == null)
			return;
		
		if (newState != null && goalstateWindow != null) {
			goalstateWindow.update(newState);
		}
		
		result.add(0, tac);
		this.lhs = this.rhs = null;
		
		exprText.setText(getCommand());
		return;
	}
	
	
	/**
	 * Updates the component
	 */
	private void update(CamlObject lhs, CamlObject rhs) throws Exception {
		if (lhs != null) {
			int nargs = lhs.camlType().numberOfArguments();
			
			if (nargs == 0) {
				if (rhs != null)
					throw new Exception("Unexpected number of arguments for newLhs = " + lhs);

				// Tactic
				if (lhs.camlType().equals(CamlType.TACTIC)) {
					evalTactic(lhs);
					return;
				}
				
				// Evaluate the expression
				rhs = lhs.eval(caml);
				if (rhs == null) {
					return;
				}
				lhs = null;
			}
			else if (nargs == 1 && rhs != null) {
				// Apply the lhs to the rhs
				rhs = lhs.apply(rhs);
				lhs = null;
				
				// Tactic
				if (rhs.camlType().equals(CamlType.TACTIC)) {
					evalTactic(rhs);
					return;
				}
				
				// Evaluate the expression
				rhs = rhs.eval(caml);
				if (rhs == null) {
					return;
				}
			}
		}
		
		this.lhs = lhs;
		this.rhs = rhs;
		
		// Update the visual components
//		result.clear();
		
		if (rhs != null)
			result.add(0, rhs);

		exprText.setText(getCommand());
	}


	@Override
	public void actionPerformed(ActionEvent e) {
		String cmd = e.getActionCommand().intern();
		
		// Clear
		if (cmd == "clear") {
			lhs = rhs = null;
			listObjects = null;
			try {
				update(lhs, rhs);
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		}
	}
}
