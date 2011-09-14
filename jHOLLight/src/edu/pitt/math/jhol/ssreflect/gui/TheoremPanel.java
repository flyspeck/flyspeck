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
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.gui.CamlObjectList;
import edu.pitt.math.jhol.gui.CamlObjectTable;

/**
 * A panel for searching theorems and saving search results
 */
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

	// The name of the configuration group
	private final static String CONF_GROUP = "theorems";
	// The configuration group
	private final Configuration.Group conf;
	
	// Commands
	private final static String ADD_TAB = "add-tab";
	private final static String REMOVE_TAB = "remove-tab";
	private final static String ACTIVATE_TAB = "activate-tab";
	private final static String SEARCH = "search";
	
	
	/**
	 * Content of each tabs
	 */
	private static class TabPanel extends JPanel {
		// The list of theorems
		private CamlObjectList theorems;
		
		/**
		 * Constructor
		 */
		public TabPanel() {
			setLayout(new BorderLayout());
			
			theorems = new CamlObjectList();
			theorems.setColumnNames("Theorem", "Name");
			JTable theoremTable = new CamlObjectTable(theorems);
			
			JScrollPane theoremScroll = new JScrollPane(theoremTable);

			add(theoremScroll, BorderLayout.CENTER);
		}
		
		
		/**
		 * Sets the theorems in the table
		 */
		public void setTheorems(ArrayList<Theorem> ths) {
			theorems.clear();
			theorems.add(ths);
		}
		
		
		/**
		 * Adds the theorem to the table
		 */
		public void addTheorem(Theorem th) {
			theorems.add(th);
		}
	}
	
	
	/**
	 * Constructor
	 */
	public TheoremPanel(Configuration configuration, CamlEnvironment caml) {
		this.conf = configuration.getGroup(CONF_GROUP);
		this.database = new TheoremDatabase(caml);
		init();
	}
	
	
	@Override
	public void save(Configuration configuration) {
//		Configuration.Group group = configuration.getGroup(CONF_GROUP);
	}
	
	
	/**
	 * Initializes all components
	 */
	private void init() {
		// Control panel
		controlPanel = new JPanel();
		BoxLayout layout = new BoxLayout(controlPanel, BoxLayout.PAGE_AXIS);
		controlPanel.setLayout(layout);
		
		// Control buttons
		// Add tab
		JButton addTab = new JButton("+");
		addTab.setActionCommand(ADD_TAB);
		addTab.addActionListener(this);
		
		// Remove tab
		JButton removeTab = new JButton("-");
		removeTab.setActionCommand(REMOVE_TAB);
		removeTab.addActionListener(this);
		
		// Activate tab
		JButton activateTab = new JButton("A");
		activateTab.setActionCommand(ACTIVATE_TAB);
		activateTab.addActionListener(this);
		
		
		controlPanel.add(addTab);
		controlPanel.add(removeTab);
		controlPanel.add(activateTab);
		
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
			tabs.add(panel, name);
			return;
		}
		
		// Remove tab
		if (cmd == REMOVE_TAB) {
			int i = tabs.getSelectedIndex();
			if (i <= 0)
				return;

			tabs.remove(i);
			return;
		}
		
		// Activate tab
		if (cmd == ACTIVATE_TAB) {
			int i = tabs.getSelectedIndex();
			if (i <= 1)
				return;
			
			// TODO: does not work as expected
/*			Component first = tabs.getComponent(1);
			Component current = tabs.getComponent(i);
			
			tabs.setComponentAt(1, current);
			tabs.add(first);*/
//			tabs.setComponentAt(i, first);
			return;
		}
		
		// Search
		if (cmd == SEARCH) {
			String text = searchField.getText();
			ArrayList<Theorem> result = database.find(text);
			searchTab.setTheorems(result);
			tabs.setSelectedComponent(searchTab);
			
			return;
		}
	}
}
