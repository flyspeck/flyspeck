package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;

import javax.swing.BoxLayout;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
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
public class TestSSReflectGUI extends JFrame implements Configuration.Saver {
	// Interprets the script
	private Interpreter interpreter;
	
	// Contains all settings
	private Configuration configuration;
	
	// Configuration group of this frame
	private static final String CONF_GROUP = "main-window";
	private static final String CONF_GROUP2 = "main-window.components";
	
	// Splitter
	private JSplitPane splitter1, splitter2, splitter3;
	
	// Displays the proof state
	private GoalstatePanel goals;
	
	// For searching theorems
	private TheoremPanel theorems;

	// The main script editor
	private TextEditor editor;
	
	// Test file
	private String fname;
	
    private JTextArea logArea;
	
	/**
	 * Constructor
	 */
	public TestSSReflectGUI(CamlEnvironment caml) {
		this.interpreter = new Interpreter(caml);
		this.configuration = new Configuration("gui.xml");
		configuration.addSaver(this);

		addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				int result = JOptionPane.showConfirmDialog(TestSSReflectGUI.this, "Save the text?", "Save", JOptionPane.YES_NO_CANCEL_OPTION);
				switch (result) {
				case JOptionPane.YES_OPTION:
					saveText(fname, editor.getText());
					break;
					
				case JOptionPane.CANCEL_OPTION:
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
		});
		
		setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
		
		// Set up the size of the window
		Configuration.Group conf = configuration.getGroup(CONF_GROUP);
		
		setPreferredSize(conf.getDimensionVal("preferred-size", 1200, 850));
		setMinimumSize(new Dimension(400, 300));

		this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));

		// Read the test file
		this.fname = "caml/test.vhl";
		String text = readText(fname);
		
		// Create the text editor
		editor = new TextEditor(interpreter, text);
		// Create the theorem panel
		theorems = new TheoremPanel(configuration, caml);

		
		initComponents();

		// Finish the initialization
		pack();
		setBounds(conf.getIntVal("x", 0), conf.getIntVal("y", 0), conf.getIntVal("w", 1200), conf.getIntVal("h", 850));
		setVisible(true);
		
/*		TheoremWindow search = new TheoremWindow(caml, this);
		search.setLocation(1200, 0);
		search.setSize(500, 700);
		search.setVisible(true);*/
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
	 * Reads all text from the given file
	 * @return
	 */
	private String readText(String fname) {
		File file = new File(fname);
		StringBuffer text = new StringBuffer();
		BufferedReader r = null;
		try {
			r = new BufferedReader(new FileReader(file));
			String separator = System.getProperty("line.separator");
		
			while (true) {
				String str = r.readLine();
				if (str == null)
					break;
			
				text.append(str);
				text.append(separator);
			}
			
			r.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		return text.toString();
	}
	
	
	/**
	 * Saves the given text in the given file
	 * @param fname
	 */
	private void saveText(String fname, String text) {
		File file = new File(fname);
		try {
			BufferedWriter w = new BufferedWriter(new FileWriter(file));
			w.write(text);
			w.close();
		}
		catch (Exception e) {
			e.printStackTrace();
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
    	public void runCommand(String rawCommand) throws Exception {
    		System.out.println("Executing: " + rawCommand);
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
		
//		final CamlEnvironment caml = new DebugCamlEnvironment((Goalstate) goal);
		final CamlEnvironment caml = new TestCamlEnvironment();
		
		
        SwingUtilities.invokeLater(new Runnable() {
        	public void run() {
        		new TestSSReflectGUI(caml);
		    }
		});
	}


}
