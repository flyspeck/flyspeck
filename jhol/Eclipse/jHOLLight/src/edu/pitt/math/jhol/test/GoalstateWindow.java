package edu.pitt.math.jhol.test;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Goal;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.core.printer.TermPrinter;

/**
 * A window which displays a goal state
 */
@SuppressWarnings("serial")
public class GoalstateWindow extends JDialog {
	// Goalstate
//	private Goalstate goalstate;
	
	private final CamlEnvironment caml;
	
	// Components
	private CamlObjectList goalsList;
	private CamlObjectList activeGoalAssumptions;
	private JLabel activeGoalText;
	
	
	
	/**
	 * Constructor
	 */
	public GoalstateWindow(CamlEnvironment caml, ExpressionBuilder builder, JFrame owner) {
		super(owner, "GoalState", false);
		this.caml = caml;
		
		builder.setGoalstateWindow(this);
		
		initInterface(builder);
	}
	
	
	/**
	 * Interface initialization
	 */
	private void initInterface(final ExpressionBuilder builder) {
		// List of goals
		goalsList = new CamlObjectList();
		final JTable goalTable = new JTable(goalsList);
		JScrollPane goalScroll = new JScrollPane(goalTable);
		goalScroll.setPreferredSize(new Dimension(500, 100));
		
		// Active goal
		activeGoalText = new JLabel("{Active goal}");
		
		// List of (active goal) assumptions
		activeGoalAssumptions = new CamlObjectList();
		final JTable assumptionTable = new JTable(activeGoalAssumptions);
		JScrollPane assumptionScroll = new JScrollPane(assumptionTable);
		assumptionScroll.setPreferredSize(new Dimension(500, 200));
		
		// Refresh button
		JButton refresh = new JButton("Refresh");
		refresh.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent arg0) {
				String cmd = "(hd o p)()";
				try {
					CamlObject obj = caml.execute(cmd, CamlType.GOAL_STATE);
					update((Goalstate) obj);
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		
		// Add everything to the window
		this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));
		this.add(goalScroll);
		this.add(activeGoalText);
		this.add(assumptionScroll);
		this.add(refresh);
		
		this.pack();
		
		
		// Register table selection listeners
		goalTable.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		goalTable.setColumnSelectionAllowed(false);
		goalTable.setRowSelectionAllowed(false);
		
		goalTable.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				if (e.getValueIsAdjusting())
					return;
				
				try {
					int index = goalTable.getSelectedRow();
					if (index < 0)
						return;
					
					CamlObject obj = goalsList.get(index);
					builder.insert(obj);
					
					goalTable.getSelectionModel().clearSelection();
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		
		
		assumptionTable.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		assumptionTable.setColumnSelectionAllowed(false);
		assumptionTable.setRowSelectionAllowed(false);
		
		assumptionTable.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				if (e.getValueIsAdjusting())
					return;
				
				try {
					int index = assumptionTable.getSelectedRow();
					if (index < 0)
						return;
					
					CamlObject obj = activeGoalAssumptions.get(index);
					builder.insert(obj);
					
					assumptionTable.getSelectionModel().clearSelection();
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		
	}
	
	
	/**
	 * Updates the window
	 */
	public void update(Goalstate state) {
		goalsList.clear();
		activeGoalText.setText("");
		activeGoalAssumptions.clear();
	
//		this.goalstate = state;
		
		if (state == null)
			return;
		
		int n = state.numberOfGoals();
		for (int i = 0; i < n; i++) {
			Goal g = state.getGoal(i);
			goalsList.add(g.goalTerm());
		}
		
		if (n > 0) {
			Goal g = state.getGoal(0);
			activeGoalText.setText(TermPrinter.print(g.goalTerm()));
			
			int k = g.numberOfAssumptions();
			for (int i = 0; i < k; i++) {
				activeGoalAssumptions.add(g.getAssumptions(i).getSecond());
			}
		}
	}
	
}
