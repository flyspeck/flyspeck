package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.PrintStream;
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
import edu.pitt.math.jhol.caml.CamlList;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlPair;
import edu.pitt.math.jhol.caml.CamlString;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.gui.CamlObjectList;
import edu.pitt.math.jhol.gui.CamlObjectTable;
import edu.pitt.math.jhol.utils.FileUtils;

/**
 * A panel for searching theorems and saving search results
 */
@SuppressWarnings("serial")
public class TheoremPanel extends JPanel implements Configuration.Saver, ActionListener {
	// For searching theorems
	private final TheoremDatabase database;
	// For working with files
	private final FileManager fileManager;
	
	// A panel with control buttons
	private JPanel controlPanel;
	
	// Main tabs
	private JTabbedPane tabs;
	// The tab for displaying search results
	private TabPanel searchTab = new TabPanel("Search");
	
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
	private final static String SAVE = "save";
	private final static String LOAD = "load";
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
		public TabPanel(String name) {
			setLayout(new BorderLayout());
			setName(name);
			
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
		
		
		/**
		 * Converts the content into a raw CAML list
		 */
		public CamlList toCamlList() {
			ArrayList<CamlPair> objs = new ArrayList<CamlPair>();
			int n = theorems.size();

			for (int i = 0; i < n; i++) {
				CamlObject obj = theorems.get(i);
				if (!(obj instanceof Theorem))
					continue;
				
				Theorem thm = (Theorem) obj;
				String name = thm.name();
				
				objs.add(new CamlPair(new CamlString(name), thm));
			}
			
			return new CamlList(new CamlType.PairType(CamlType.STRING, CamlType.THM), objs);
		}
	}
	
	
	/**
	 * Constructor
	 */
	public TheoremPanel(Configuration configuration, CamlEnvironment caml, FileManager fileManager) {
		Configuration.Group conf = configuration.getGroup(CONF_GROUP);
		this.database = new TheoremDatabase(caml);
		this.fileManager = fileManager;
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
		
		// Save
		JButton save = new JButton("Save");
		save.setActionCommand(SAVE);
		save.addActionListener(this);
		save.setMaximumSize(max);

		// Load
		JButton load = new JButton("Load");
		load.setActionCommand(LOAD);
		load.addActionListener(this);
		load.setMaximumSize(max);
		
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
		
		controlPanel.add(save);
		controlPanel.add(load);
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
	
	
	/**
	 * Saves the content of tabs in a file
	 */
	private void saveTabs() {
		// Select a file first
		File file = FileUtils.saveFileDialog(fileManager.getCurrentDir(), "txt", null);
		if (file == null)
			return;

		try {
			PrintStream out = new PrintStream(file);
			
			// Save all tabs (except the search tab)
			for (int i = 1; i < tabs.getTabCount(); i++) {
				Component c = tabs.getComponentAt(i);
				if (!(c instanceof TabPanel))
					continue;
				
				TabPanel tab = (TabPanel) c;
			
				// Save the tab name
				out.println("Tab: " + tab.getName());
				
				// Save the tab content
				out.println(tab.toCamlList().toRawString());
			}
			
			out.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Loads tabs
	 */
	private void loadTabs() {
		// Select a file
		File file = FileUtils.saveFileDialog(fileManager.getCurrentDir(), "txt", null);
		if (file == null)
			return;
		
		// Remove all tabs
		tabs.removeAll();
		tabs.addTab(searchTab.getName(), searchTab);
		activeTab = null;
		
		ArrayList<String> rows = FileUtils.readFile(file);
		int n = rows.size();
		
		for (int i = 0; i < n; i++) {
			String row = rows.get(i);
			if (row == null)
				continue;
			
			// Tab
			if (row.startsWith("Tab: ")) {
				String name = row.substring("Tab: ".length());
				String content = null;
				
				if (i < n - 1) {
					i += 1;
					content = rows.get(i);
				}
				
				TabPanel tab = new TabPanel(name);
				
				if (content != null) {
					ArrayList<Theorem> thms = database.parse(content);
					tab.setItems(thms);
				}
				
				tabs.addTab(tab.getName(), tab);
			}
		}
	}
	

	@Override
	public void actionPerformed(ActionEvent arg) {
		String cmd = arg.getActionCommand();
		if (cmd == null)
			return;
		
		cmd = cmd.intern();
		
		// Save
		if (cmd == SAVE) {
			saveTabs();
			return;
		}
		
		// Load
		if (cmd == LOAD) {
			loadTabs();
			return;
		}
		
		// Add tab
		if (cmd == ADD_TAB) {
			String name = JOptionPane.showInputDialog("Input new tab name: ");
			if (name == null) {
				return;
			}
			
			if (name.length() == 0)
				name = "Tab " + tabs.getTabCount();
			
			JPanel panel = new TabPanel(name);
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
