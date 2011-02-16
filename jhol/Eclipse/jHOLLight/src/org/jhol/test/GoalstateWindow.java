package org.jhol.test;

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

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.Goal;
import org.jhol.core.Goalstate;
import org.jhol.core.printer.TermPrinter;

/**
 * A window which displays a goal state
 */
@SuppressWarnings("serial")
public class GoalstateWindow extends JDialog {
	// Goalstate
	private Goalstate goalstate;
	
	private final CamlEnvironment caml;
	
	// Components
	private CamlObjectList goalsList;
	private CamlObjectList activeGoalAssumptions;
	private JLabel activeGoalText;
	
	
	
	/**
	 * Constructor
	 */
	public GoalstateWindow(CamlEnvironment caml, JFrame owner) {
		super(owner, "GoalState", false);
		this.caml = caml;
		
		initInterface();
	}
	
	
	/**
	 * Interface initialization
	 */
	private void initInterface() {
		// List of goals
		goalsList = new CamlObjectList();
		JTable goalTable = new JTable(goalsList);
		JScrollPane goalScroll = new JScrollPane(goalTable);
		goalScroll.setPreferredSize(new Dimension(500, 100));
		
		// Active goal
		activeGoalText = new JLabel("{Active goal}");
		
		// List of (active goal) assumptions
		activeGoalAssumptions = new CamlObjectList();
		JTable assumptionTable = new JTable(activeGoalAssumptions);
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
	}
	
	
	/**
	 * Updates the window
	 */
	public void update(Goalstate state) {
		goalsList.clear();
		activeGoalText.setText("");
		activeGoalAssumptions.clear();
	
		this.goalstate = state;
		
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
