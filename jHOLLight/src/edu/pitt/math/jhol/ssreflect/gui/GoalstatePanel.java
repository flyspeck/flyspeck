package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.Dimension;
import java.util.ArrayList;

import javax.swing.BoxLayout;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;

import edu.pitt.math.jhol.core.Goal;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.core.Pair;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.gui.CamlObjectComponent;
import edu.pitt.math.jhol.gui.CamlObjectList;
import edu.pitt.math.jhol.gui.CamlObjectTable;

/**
 * Contains information about the current goal and all other goals
 */
@SuppressWarnings("serial")
public class GoalstatePanel extends JPanel {
	// Goal state
	private Goalstate goalstate;
	
	// Tabs for all goals
	private JTabbedPane tabs;


	/**
	 * A component for each goal
	 */
	private static class GoalInfo extends JPanel {
		// Goal's free variables
		private CamlObjectList goalVars;
		// Goal's assumptions
		private CamlObjectList goalAssumptions;
		// Goal's term
		private CamlObjectComponent activeGoal;
		
		/**
		 * Constructor
		 */
		public GoalInfo(Goal goal) {
			initInterface();
			update(goal);
		}

		
		/**
		 * Updates the component
		 */
		public void update(Goal goal) {
			goalVars.clear();
			goalAssumptions.clear();
			
			// Update variables
			ArrayList<Term> vars = goal.getContextVariables();
			for (Term var : vars) {
				goalVars.add(var);
			}
			
			// Update assumptions
			int n = goal.numberOfAssumptions();
			for (int i = 0; i < n; i++) {
				Pair<String, Theorem> assumption = goal.getAssumptions(i);
				goalAssumptions.add(assumption.getSecond());
			}
			
			// Update the goal
			activeGoal.init(goal.goalTerm());
		}
		
		
		/**
		 * Initializes the components
		 */
		private void initInterface() {
			// List of free variables
			goalVars = new CamlObjectList();
			JTable varTable = new CamlObjectTable(goalVars); 
			JScrollPane varScroll = new JScrollPane(varTable);
			varScroll.setPreferredSize(new Dimension(500, 200));
			
			// List of assumptions
			goalAssumptions = new CamlObjectList();
			JTable assumptionTable = new CamlObjectTable(goalAssumptions); 
			JScrollPane assumptionScroll = new JScrollPane(assumptionTable);
			assumptionScroll.setPreferredSize(new Dimension(500, 500));
			
			// Active goal
			activeGoal = new CamlObjectComponent(true, true, false);

			// Add components
			BoxLayout layout = new BoxLayout(this, BoxLayout.PAGE_AXIS);
			this.setLayout(layout);
			this.add(varScroll);
			this.add(assumptionScroll);
			this.add(activeGoal);
		}
	}
	
	/**
	 * Constructor
	 */
	public GoalstatePanel() {
		tabs = new JTabbedPane();
		add(tabs);
	}
	
	
	/**
	 * Updates the component
	 */
	public void update(Goalstate state) {
		this.goalstate = state;
		
		tabs.removeAll();
		int n = state.numberOfGoals();
		
		for (int i = 0; i < n; i++) {
			Goal g = state.getGoal(i);
			GoalInfo info = new GoalInfo(g);
			tabs.add(info);
		}
	}
		
}
