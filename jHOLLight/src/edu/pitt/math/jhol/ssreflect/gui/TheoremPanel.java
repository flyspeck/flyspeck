package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextField;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.gui.CamlObjectList;
import edu.pitt.math.jhol.gui.CamlObjectTable;

/**
 * A panel for searching theorems and saving search results
 */
@SuppressWarnings("serial")
public class TheoremPanel extends JPanel implements Configuration.Saver, ActionListener {
	// For searching theorems
	private final TheoremDatabase database;
	
	// A panel with control buttons
	private JPanel controlPanel;
	
	// Main tabs
	private JTabbedPane tabs;
	// The tab for displaying search results
	private TabPanel searchTab = new TabPanel();
	
	// A field for search inputs
	private JTextField searchField;
	
	// The active tab
	private TabPanel activeTab;

	// The name of the configuration group
	private final static String CONF_GROUP = "theorems";
	
	// Commands
	private final static String ADD_TAB = "add-tab";
	private final static String REMOVE_TAB = "remove-tab";
	private final static String ACTIVATE_TAB = "activate-tab";
	private final static String MOVE_THM = "move-theorem"; 
	private final static String SEARCH = "search";
	
	
	/**
	 * Content of each tabs
	 */
	private static class TabPanel extends JPanel {
		// The list of theorems
		private final CamlObjectList theorems;
		// The table with theorems
		private final JTable theoremTable;
		
		/**
		 * Constructor
		 */
		public TabPanel() {
			setLayout(new BorderLayout());
			
			theorems = new CamlObjectList();
			theorems.setColumnNames("Theorem", "Name");
			theoremTable = new CamlObjectTable(theorems);
			
			JScrollPane theoremScroll = new JScrollPane(theoremTable);

			add(theoremScroll, BorderLayout.CENTER);
		}
		
		/**
		 * Sets the objects in the table
		 */
		public void setItems(ArrayList<? extends CamlObject> objs) {
			theorems.clear();
			theorems.add(objs);
		}
		
		/**
		 * Adds the given object to the table
		 */
		public void addItems(ArrayList<? extends CamlObject> objs) {
			theorems.add(objs);
		}
		
		
		/**
		 * Removes the given objects from the table
		 */
		public void removeItems(ArrayList<? extends CamlObject> objs) {
			theorems.remove(objs);
		}
		
		
		/**
		 * Returns all objects corresponding to selected table rows
		 */
		public ArrayList<CamlObject> getSelectedItems() {
			ArrayList<CamlObject> result = new ArrayList<CamlObject>();
			int[] rows = theoremTable.getSelectedRows();

			if (rows != null) {
				for (int i : rows) {
					CamlObject obj = theorems.get(i);
					if (obj != null)
						result.add(obj);
				}
			}
			
			return result;
		}
	}
	
	
	/**
	 * Constructor
	 */
	public TheoremPanel(Configuration configuration, CamlEnvironment caml) {
		Configuration.Group conf = configuration.getGroup(CONF_GROUP);
		this.database = new TheoremDatabase(caml);
		init(conf);
	}
	
	
	@Override
	public void save(Configuration configuration) {
//		Configuration.Group group = configuration.getGroup(CONF_GROUP);
	}
	
	
	/**
	 * Initializes all components
	 */
	private void init(Configuration.Group conf) {
		// Control panel
		controlPanel = new JPanel();
//		GridLayout layout = new GridLayout(0, 1);
		BoxLayout layout = new BoxLayout(controlPanel, BoxLayout.PAGE_AXIS);
		controlPanel.setLayout(layout);
		
		// Control buttons
		Dimension max = new Dimension(1000, 30);
		
		// Add tab
		JButton addTab = new JButton("+");
		addTab.setActionCommand(ADD_TAB);
		addTab.addActionListener(this);
		addTab.setMaximumSize(max);
		
		// Remove tab
		JButton removeTab = new JButton("-");
		removeTab.setActionCommand(REMOVE_TAB);
		removeTab.addActionListener(this);
		removeTab.setMaximumSize(max);
		
		// Activate tab
		JButton activateTab = new JButton("A");
		activateTab.setActionCommand(ACTIVATE_TAB);
		activateTab.addActionListener(this);
		activateTab.setMaximumSize(max);
		
		// Move theorem
		JButton moveThm = new JButton("->");
		moveThm.setActionCommand(MOVE_THM);
		moveThm.addActionListener(this);
		moveThm.setMaximumSize(max);
		
		
		controlPanel.add(addTab);
		controlPanel.add(removeTab);
		controlPanel.add(activateTab);
		controlPanel.add(moveThm);
		
		// Search field
		searchField = new JTextField();
		searchField.setActionCommand(SEARCH);
		searchField.addActionListener(this);
		
		// Main tabs
		tabs = new JTabbedPane();
		tabs.add(searchTab, "Search");
		
		// Finalize the initialization
		this.setLayout(new BorderLayout());
		
		this.add(controlPanel, BorderLayout.WEST);
		this.add(searchField, BorderLayout.SOUTH);
		this.add(tabs, BorderLayout.CENTER);
	}


	/**
	 * Activates the selected tab
	 */
	private void activateTab() {
		int i = tabs.getSelectedIndex();
		if (i <= 0)
			return;
		
		Component tab = tabs.getSelectedComponent();
		if (!(tab instanceof TabPanel))
			return;
		
		if (tab == activeTab)
			return;
		
		String name;
		
		// Deactivate the active tab
		if (activeTab != null) {
			name = activeTab.getName();
			int j = tabs.indexOfComponent(activeTab);

			if (j >= 0) {
				tabs.setTitleAt(j, name);
			}
			
			activeTab = null;
		}
		
		// Activate the selected tab
		name = "*" + tab.getName() + "*";
		activeTab = (TabPanel) tab;
		tabs.setTitleAt(i, name);
	}
	
	
	/**
	 * Moves selected theorems to the active tab
	 */
	private void moveSelected() {
		if (activeTab == null)
			return;

		Component c = tabs.getSelectedComponent();
		if (!(c instanceof TabPanel))
			return;
		
		TabPanel selectedTab = (TabPanel) c;
		if (selectedTab == activeTab)
			return;
		
		ArrayList<CamlObject> items = selectedTab.getSelectedItems();
		activeTab.addItems(items);
		selectedTab.removeItems(items);
	}
	

	@Override
	public void actionPerformed(ActionEvent arg) {
		String cmd = arg.getActionCommand();
		if (cmd == null)
			return;
		
		cmd = cmd.intern();
		
		// Add tab
		if (cmd == ADD_TAB) {
			String name = JOptionPane.showInputDialog("Input new tab name: ");
			if (name == null) {
				return;
			}
			
			if (name.length() == 0)
				name = "Tab " + tabs.getTabCount();
			
			JPanel panel = new TabPanel();
			panel.setName(name);
			tabs.addTab(name, panel);
			return;
		}
		
		// Remove tab
		if (cmd == REMOVE_TAB) {
			int i = tabs.getSelectedIndex();
			if (i <= 0)
				return;
			
			if (activeTab == tabs.getSelectedComponent())
				activeTab = null;

			tabs.removeTabAt(i);
			return;
		}
		
		// Activate tab
		if (cmd == ACTIVATE_TAB) {
			activateTab();
			return;
		}
		
		// Move selected theorems to the active tab
		if (cmd == MOVE_THM) {
			moveSelected();
			return;
		}
		
		// Search
		if (cmd == SEARCH) {
			String text = searchField.getText();
			ArrayList<Theorem> result = database.find(text);
			searchTab.setItems(result);
			tabs.setSelectedComponent(searchTab);
			
			return;
		}
	}
}
