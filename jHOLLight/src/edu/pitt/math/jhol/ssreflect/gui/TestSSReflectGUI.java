package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;

import javax.swing.BoxLayout;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.core.parser.Parser;
import edu.pitt.math.jhol.core.printer.TermPrinterData;
import edu.pitt.math.jhol.ssreflect.parser.Interpreter;
import edu.pitt.math.jhol.test.TestCamlEnvironment;

/**
 * Test GUI
 * @author Alexey
 *
 */
@SuppressWarnings("serial")
public class TestSSReflectGUI extends JFrame implements Configuration.Saver, ActionListener {
	// Interprets the script
	private final Interpreter interpreter;
	
	// Contains all settings
	private final Configuration configuration;
	
	// File manager
	private final FileManager fileManager;
	
	// Configuration group of this frame
	private static final String CONF_GROUP = "main-window";
	private static final String CONF_GROUP2 = "main-window.components";
	
	// Commands
	private static final String CMD_FILE_NEW = "file-new";
	private static final String CMD_FILE_OPEN = "file-open";
	private static final String CMD_FILE_SAVE = "file-save";
	private static final String CMD_FILE_SAVE_AS = "file-save-as";
	private static final String CMD_FILE_EXIT = "file-exit";
	
	// File menu
	private JMenu fileMenu;
	
	// Splitter
	private JSplitPane splitter1, splitter2, splitter3;
	
	// Displays the proof state
	private GoalstatePanel goals;
	
	// For searching theorems
	private TheoremPanel theorems;

	// The main script editor
	private TextEditor editor;
	
    private JTextArea logArea;
	
	/**
	 * Constructor
	 */
	public TestSSReflectGUI(CamlEnvironment caml) {
		this.interpreter = new Interpreter(caml, "caml/test.log");
		this.configuration = new Configuration("gui.xml");
		configuration.addSaver(this);

		addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				exit();
			}			
		});
		
		setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
		
		// Set up the size of the window
		Configuration.Group conf = configuration.getGroup(CONF_GROUP);
		
		setPreferredSize(conf.getDimensionVal("preferred-size", 1200, 850));
		setMinimumSize(new Dimension(400, 300));

		this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));
		setBounds(conf.getIntVal("x", 0), conf.getIntVal("y", 0), conf.getIntVal("w", 1200), conf.getIntVal("h", 850));

		// Create the text editor
		editor = new TextEditor(interpreter);
		
		editor.addListener(new TextEditor.Listener() {
			@Override
			public void modified(boolean modifiedFlag) {
				String title = getTitle();
				if (title == null || title.length() == 0)
					title = "New";
				
				if (title.charAt(title.length() - 1) == '*')
					title = title.substring(0, title.length() - 1);
				
				if (modifiedFlag)
					title += "*";
				
				setTitle(title);
			}
		});
		
		// Create the theorem panel
		theorems = new TheoremPanel(configuration, caml);

		
		initComponents();
		createMenu();
		
		// Create the file manager
		this.fileManager = new FileManager(configuration, fileMenu, this);
		configuration.addSaver(fileManager);
		
		fileManager.addCurrentFileListener(new FileManager.CurrentFileListener() {
			@Override
			public void currentFileChanged(File currentFile) {
				String name = (currentFile == null) ? "New" : currentFile.getAbsolutePath();
				setTitle(name);
			}
		});
		
		setTitle("New");
		
		if (fileManager.getCurrentFile() != null) {
			String text = fileManager.readCurrent();
			setNewText(text);
			setTitle(fileManager.getCurrentFile().getAbsolutePath());
		}

		// Finish the initialization
		setVisible(true);
	}
	
	
	@Override
	public void save(Configuration conf) {
		Configuration.Group group = conf.getGroup(CONF_GROUP);
		// Preferred size
		group.setVal("preferred-size", getPreferredSize());
		
		// Location and size
		Point p = getLocation();
		Dimension s = getSize();
		group.setVal("x", p.x);
		group.setVal("y", p.y);
		group.setVal("w", s.width);
		group.setVal("h", s.height);
		
		// Splitters
		group = conf.getGroup(CONF_GROUP2);
		group.setVal("split1", splitter1.getDividerLocation());
		group.setVal("split2", splitter2.getDividerLocation());
		group.setVal("split3", splitter3.getDividerLocation());
	}
	
	
	/**
	 * Sets the new text in the editor and resets the interpreter
	 */
	private void setNewText(String text) {
		String logName = "caml/test.log";
		
		if (fileManager.getCurrentFile() != null) {
			logName = fileManager.getCurrentFile().getName() + ".log";
		}

		if (text != null) {
			editor.initText(text);
			interpreter.clearAndInit(logName);
		}
	}

   
	/**
	 * Initializes components
	 */
    private void initComponents() {
    	// Initialize the text editor
        editor.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 14));
        
        // Initialize the log area
        logArea = new JTextArea();
        logArea.setEditable(false);
        logArea.setColumns(80);
        logArea.setLineWrap(true);
        logArea.setRows(100);
        logArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 16));

        // Initialize the goal panel
        goals = new GoalstatePanel(configuration);
		// Add a goal update listener
		interpreter.addGoalListener(new Interpreter.GoalListener() {
			@Override
			public void updateGoal(Goalstate state) {
				goals.update(state);
			}
		});
		
		// Initialize the theorem panel

        
        // Finish the initialization
        JScrollPane textScroll = new JScrollPane(editor);
        textScroll.setPreferredSize(new Dimension(700, 600));
        textScroll.setMinimumSize(new Dimension(500, 500));
        JScrollPane logScroll = new JScrollPane(logArea);
        logScroll.setPreferredSize(new Dimension(500, 200));
        
        splitter1 = new JSplitPane(JSplitPane.VERTICAL_SPLIT, textScroll, logScroll);
        splitter3 = new JSplitPane(JSplitPane.VERTICAL_SPLIT, goals, theorems);
        splitter2 = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, splitter1, splitter3);
        
        // Configure splitters
        Configuration.Group group = configuration.getGroup(CONF_GROUP2);
        splitter1.setDividerLocation(group.getIntVal("split1", 100));
        splitter2.setDividerLocation(group.getIntVal("split2", 100));
        splitter3.setDividerLocation(group.getIntVal("split3", 100));
        
        add(splitter2);
    }
    
    
    /**
     * Creates the main menu
     */
    private void createMenu() {
    	JMenuBar menuBar;
    	JMenu menu;
    	JMenuItem menuItem;

    	// Create the menu bar.
    	menuBar = new JMenuBar();

    	// Build the File menu.
    	menu = new JMenu("File");
    	menu.setMnemonic(KeyEvent.VK_F);
    	menuBar.add(menu);

    	// Menu items
    	// New
    	menuItem = new JMenuItem("New",
    	                         KeyEvent.VK_N);
    	menuItem.setActionCommand(CMD_FILE_NEW);
    	menuItem.addActionListener(this);
    	menu.add(menuItem);

    	// Open
    	menuItem = new JMenuItem("Open...",
    	                         KeyEvent.VK_O);
    	menuItem.setActionCommand(CMD_FILE_OPEN);
    	menuItem.addActionListener(this);
    	menu.add(menuItem);

    	// Save
    	menuItem = new JMenuItem("Save", KeyEvent.VK_S);
    	menuItem.setAccelerator(KeyStroke.getKeyStroke(
    	        KeyEvent.VK_S, ActionEvent.CTRL_MASK));
    	menuItem.setActionCommand(CMD_FILE_SAVE);
    	menuItem.addActionListener(this);
    	menu.add(menuItem);

    	// Save as
    	menuItem = new JMenuItem("Save as...");
    	menuItem.setAccelerator(KeyStroke.getKeyStroke(
    	        KeyEvent.VK_S, ActionEvent.CTRL_MASK | ActionEvent.SHIFT_MASK));
    	menuItem.setActionCommand(CMD_FILE_SAVE_AS);
    	menuItem.addActionListener(this);
    	menu.add(menuItem);
    	
    	// Exit
    	menu.addSeparator();
    	
    	menuItem = new JMenuItem("Exit", KeyEvent.VK_X);
    	menuItem.setActionCommand(CMD_FILE_EXIT);
    	menuItem.addActionListener(this);
    	menu.add(menuItem);

    	this.fileMenu = menu;
    	
    	// Finish the menu initialization
    	menuBar.add(menu);
    	this.setJMenuBar(menuBar);    	
    }
    
    

    @Override
	public void actionPerformed(ActionEvent e) {
		String cmd = e.getActionCommand();
		if (cmd == null)
			return;
		
		cmd = cmd.intern();
		
		// Exit
		if (cmd == CMD_FILE_EXIT) {
			exit();
			return;
		}
		
		// New
		if (cmd == CMD_FILE_NEW) {
			if (!saveModified()) {
				return;
			}
			
			fileManager.setCurrentFile(null);
			setNewText("");
			return;
		}
		
		// Open
		if (cmd == CMD_FILE_OPEN) {
			if (!saveModified()) {
				return;
			}
			
			String text = fileManager.openAndRead();
			setNewText(text);
			return;
		}
		
		// Save
		if (cmd == CMD_FILE_SAVE) {
			if (fileManager.saveCurrent(editor.getText()))
				editor.setModified(false);
			return;
		}
		
		// Save as
		if (cmd == CMD_FILE_SAVE_AS) {
			if (fileManager.saveAs(editor.getText()))
				editor.setModified(false);
			return;
		}
		
		// Recently open file
		if (cmd.startsWith(FileManager.CMD_FILE_RECENT)) {
			String name = cmd.substring(FileManager.CMD_FILE_RECENT.length());
			if (!saveModified()) {
				return;
			}
			
			fileManager.setCurrentFile(new File(name));
			setNewText(fileManager.readCurrent());
			return;
		}
	}
    
    
    /**
     * Shows a dialog for saving the modified text.
     * Returns false if a user selects the 'Cancel' option
     */
    private boolean saveModified() {
		if (editor.isModified()) {
			int result = JOptionPane.showConfirmDialog(TestSSReflectGUI.this, "Save the text?", "Save", JOptionPane.YES_NO_CANCEL_OPTION);
			switch (result) {
			case JOptionPane.YES_OPTION:
				fileManager.saveCurrent(editor.getText());
				break;
			
			case JOptionPane.CANCEL_OPTION:
				return false;
			}
		}
		
		return true;
    }
    
    
    
    /**
     * Exits the program
     */
    private void exit() {
    	if (!saveModified()) {
    		return;
    	}

		// Save the configuration
		try {
			configuration.updateAndSave();
		}
		catch (Exception ex) {
			ex.printStackTrace();
		}
		
		// Exit
		System.exit(0);
    }

   
    
    
    /**
     * A Caml environment for test purposes
     * @author Alexey
     *
     */
    static class DebugCamlEnvironment extends CamlEnvironment {
    	private final Goalstate testGoalstate;
    	
    	public DebugCamlEnvironment(Goalstate test) {
    		this.testGoalstate = test;
    	}
    	
    	@Override
    	public CamlObject execute(String command) throws Exception {
    		throw new Exception("execute(String): Not implemented");
    	}

    	@Override
    	public CamlObject execute(String command, CamlType returnType)
    			throws Exception {
    		System.out.println("Executing: " + command);
    		
    		if (returnType.equals(CamlType.GOAL_STATE)) {
    			return testGoalstate;
    		}
    		
    		return null;
    	}

    	@Override
    	public String runCommand(String rawCommand) throws Exception {
    		System.out.println("Executing: " + rawCommand);
    		return "";
    	}
    	
    }
    
 
	
	
	/**
	 * Main function
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
		TermPrinterData.init();
		
		String testGoal = "Goalstate(List(Goal,[Goal(List(Pair(String,Theorem),[Pair(\"t0\",Theorem(List(Term,[Comb(Comb(Const(\"real_lt\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Var(\"t\",Tyapp(\"real\"[])))]),Comb(Comb(Const(\"real_lt\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Var(\"t\",Tyapp(\"real\"[])))));Pair(\"qf\",Theorem(List(Term,[Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"q\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"q\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))));Pair(\"pf\",Theorem(List(Term,[Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))));Pair(\"f'P\",Theorem(List(Term,[Comb(Comb(Const(\"facet_of\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Comb(Const(\"facet_of\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))));Pair(\"fP\",Theorem(List(Term,[Comb(Comb(Const(\"facet_of\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Comb(Const(\"facet_of\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))));Pair(\"p0_ff'\",Theorem(List(Term,[Comb(Const(\"~\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Comb(Comb(Const(\"UNION\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))))]),Comb(Const(\"~\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Comb(Comb(Const(\"UNION\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Var(\"f\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"f'\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))))));Pair(\"p0P\",Theorem(List(Term,[Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))));Pair(\"polyP\",Theorem(List(Term,[Comb(Const(\"polyhedron\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))]),Comb(Const(\"polyhedron\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Var(\"P\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))))]),Comb(Comb(Const(\"==>\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"real_lt\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Var(\"s\",Tyapp(\"real\"[])))),Comb(Comb(Const(\"==>\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"vector_add\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Comb(Const(\"real_sub\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Var(\"t\",Tyapp(\"real\"[])))),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Var(\"t\",Tyapp(\"real\"[]))),Var(\"p\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))))),Comb(Comb(Const(\"vector_add\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Comb(Const(\"real_sub\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Var(\"s\",Tyapp(\"real\"[])))),Var(\"p0\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Var(\"s\",Tyapp(\"real\"[]))),Var(\"q\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))))),Comb(Comb(Const(\"real_le\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Var(\"s\",Tyapp(\"real\"[]))),Var(\"t\",Tyapp(\"real\"[]))))))]))";
		final CamlObject goal = Parser.parse(testGoal);
		
		final CamlEnvironment caml = new DebugCamlEnvironment((Goalstate) goal);
//		final CamlEnvironment caml = new TestCamlEnvironment();
		
		
        SwingUtilities.invokeLater(new Runnable() {
        	public void run() {
        		new TestSSReflectGUI(caml);
		    }
		});
	}


}
