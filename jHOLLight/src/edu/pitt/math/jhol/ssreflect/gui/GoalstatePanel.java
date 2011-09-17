package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.util.ArrayList;

import javax.swing.BoxLayout;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.table.TableColumnModel;

import edu.pitt.math.jhol.core.Goal;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.core.Pair;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.gui.CamlObjectList;
import edu.pitt.math.jhol.gui.CamlObjectTable;

/**
 * Contains information about the current goal and all other goals
 */
@SuppressWarnings("serial")
public class GoalstatePanel extends JPanel implements Configuration.Saver {
	// Tabs for all goals
	private JTabbedPane tabs;
	
	// The name of the configuration group
	private static final String CONF_GROUP = "goalstate-panel";
	
	// Configuration group
	private Configuration.Group conf;
	
	// List of goal descriptions
	private final ArrayList<GoalInfo> goalDescriptions = new ArrayList<GoalInfo>();


	/**
	 * A component for each goal
	 */
	private static class GoalInfo extends JPanel {
		// Goal's free variables
		private CamlObjectList goalVars;
		// Goal's assumptions
		private CamlObjectList goalAssumptions;
		// Goal's term
		private CamlObjectList activeGoal;
		
		// Splitters
		private JSplitPane splitter1, splitter2;
		
		/**
		 * Constructor
		 */
		public GoalInfo(Configuration.Group group) {
			initInterface(group);
		}
		
		/**
		 * Saves information in the given configuration group
		 */
		public void save(Configuration.Group group) {
			group.setVal("split1", splitter1.getDividerLocation());
			group.setVal("split2", splitter2.getDividerLocation());
		}
		
		/**
		 * Updates the component
		 */
		public void update(Goal goal) {
			goalVars.clear();
			goalAssumptions.clear();
			activeGoal.clear();
			
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
			activeGoal.add(goal.goalTerm());
		}
		
		
		/**
		 * Initializes the components
		 */
		private void initInterface(Configuration.Group group) {
			// List of free variables
			goalVars = new CamlObjectList();
			goalVars.setColumnNames("Variable", "Type");
			JTable varTable = new CamlObjectTable(goalVars); 

			TableColumnModel model = varTable.getColumnModel();
			model.getColumn(0).setPreferredWidth(100);
			model.getColumn(0).setWidth(100);
			model.getColumn(1).setPreferredWidth(400);
			model.getColumn(1).setWidth(400);
			varTable.setShowVerticalLines(false);
			
			
			JScrollPane varScroll = new JScrollPane(varTable);
			varScroll.setPreferredSize(new Dimension(500, 200));
			
			// List of assumptions
			goalAssumptions = new CamlObjectList();
			goalAssumptions.setColumnNames("Assumption", "Label");
			JTable assumptionTable = new CamlObjectTable(goalAssumptions);
			
			assumptionTable.getColumnModel().getColumn(0).setPreferredWidth(400);
			assumptionTable.getColumnModel().getColumn(1).setPreferredWidth(100);
			assumptionTable.getColumnModel().moveColumn(1, 0);
			assumptionTable.setShowVerticalLines(false);
			
			JScrollPane assumptionScroll = new JScrollPane(assumptionTable);
			assumptionScroll.setPreferredSize(new Dimension(500, 300));
			
			// Active goal
			activeGoal = new CamlObjectList(true, false);
			activeGoal.setColumnNames("Goal", null);
			JTable goalTable = new CamlObjectTable(activeGoal); 
			JScrollPane goalScroll = new JScrollPane(goalTable);
			goalScroll.setPreferredSize(new Dimension(500, 100));

			// Add components
			BoxLayout layout = new BoxLayout(this, BoxLayout.PAGE_AXIS);
			this.setLayout(layout);
			
			splitter1 = new JSplitPane(JSplitPane.VERTICAL_SPLIT, varScroll, assumptionScroll);
			splitter2 = new JSplitPane(JSplitPane.VERTICAL_SPLIT, splitter1, goalScroll);
			
			splitter1.setDividerLocation(group.getIntVal("split1", 100));
			splitter2.setDividerLocation(group.getIntVal("split2", 100));

			this.add(splitter2);
		}
	}
	
	/**
	 * Constructor
	 */
	public GoalstatePanel(Configuration configuration) {
		conf = configuration.getGroup(CONF_GROUP);
		configuration.addSaver(this);
		
		tabs = new JTabbedPane();
		this.setLayout(new BorderLayout());
		add(tabs, BorderLayout.CENTER);
	}
	
	
	@Override
	public void save(Configuration configuration) {
		Configuration.Group group = configuration.getGroup(CONF_GROUP);
		if (goalDescriptions.size() > 0) {
			goalDescriptions.get(0).save(group);
		}
	}
	
	
	/**
	 * Returns the i-th goal description.
	 * Initializes the i-th goal description if necessary
	 * @param i
	 * @return
	 */
	private GoalInfo getDescription(int i) {
		if (i < 0 || i > 100)
			return null;

		int n = goalDescriptions.size();
		if (i >= n) {
			// Initialize descriptions
			for (int j = n; j <= i; j++) {
				GoalInfo info = new GoalInfo(conf);
				goalDescriptions.add(info);
			}
		}
		
		return goalDescriptions.get(i);
	}
	
	
	/**
	 * Updates the component
	 */
	public void update(Goalstate state) {
		tabs.removeAll();
		if (state == null)
			return;
		
		int n = state.numberOfGoals();
		
		for (int i = 0; i < n; i++) {
			Goal g = state.getGoal(i);
			
			GoalInfo info = getDescription(i);
			info.update(g);
			info.setName("Goal " + (i + 1));

			tabs.add(info);
		}
	}
		
}
