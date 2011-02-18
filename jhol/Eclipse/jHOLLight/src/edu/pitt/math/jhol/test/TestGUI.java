package edu.pitt.math.jhol.test;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlFunction;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.core.lexer.Parser;
import edu.pitt.math.jhol.core.printer.TermPrinterData;

/**
 * Test GUI
 * @author Alexey
 *
 */
@SuppressWarnings("serial")
public class TestGUI extends JFrame implements ActionListener {
	private CamlEnvironment caml;
	
//	private TermList terms;
	private CamlObjectList terms;
	private JTextField termField;
	
	// Arbitrary command
	private JTextField commandField;
	
	private ExpressionBuilder builder;
	
	/**
	 * Constructor
	 */
	public TestGUI(CamlEnvironment caml) {
		this.caml = caml;
		
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setPreferredSize(new Dimension(500, 300));
		setMinimumSize(new Dimension(400, 300));

		this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));
		
		initInterface();
		
		pack();
		setVisible(true);
		
		// Create an expression builder
		builder = new ExpressionBuilder(this, caml);
		
		JDialog dialog = new JDialog(this, false);
		dialog.add(builder);
		dialog.pack();
		dialog.setVisible(true);
		dialog.setLocation(500, 0);
		
		// Create a TheoremWindow
		TheoremWindow win = new TheoremWindow(caml, builder, this);
		win.setLocation(300, dialog.getHeight());
		win.pack();
		win.setVisible(true);
		
		// Create a GoalstateWindow
		GoalstateWindow win2 = new GoalstateWindow(caml, builder, this);
		win2.setLocation(500, dialog.getHeight());
		win2.pack();
		win2.setVisible(true);
	}
	
	
	/**
	 * Initializes the user interface
	 */
	private void initInterface() {
		// A table of terms
//		terms = new TermList();
		terms = new CamlObjectList();
		final JTable termsTable = new JTable(terms);

		termsTable.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		termsTable.setColumnSelectionAllowed(false);
		termsTable.setRowSelectionAllowed(false);
		
		termsTable.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				if (e.getValueIsAdjusting())
					return;
				
				try {
					int index = termsTable.getSelectedRow();
					if (index < 0)
						return;
					
					CamlObject obj = terms.get(index);
					builder.insert(obj);
					
					termsTable.getSelectionModel().clearSelection();
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		
		JScrollPane scroll = new JScrollPane(termsTable);
		
		add(scroll);
		
		// A field for entering new terms
		termField = new JTextField();
		termField.addActionListener(this);
		
		// A field for entering Caml commands
		commandField = new JTextField();
		commandField.addActionListener(this);
		
		add(termField);
		add(commandField);
	}
	

	/**
	 * Action listener
	 */
	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == termField) {
			// Term field
			String termString = termField.getText();
			String cmd = "`" + termString + "`";
			
			try {
				CamlObject obj = caml.execute(cmd, CamlType.TERM);
				if (!(obj instanceof Term))
					return;
				
				Term term = (Term) obj;
				terms.add(term);
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		}
		else if (e.getSource() == commandField) {
			// Command field
			String cmd = commandField.getText() + ";;";
			try {
				caml.runCommand(cmd);
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		}
	}

	
	/**
	 * Returns the list of terms
	 */
	public CamlObjectList getTerms() {
		return terms;
	}
	
	
	/**
	 * Creates a window for functions
	 */
	public void createFunctions(CamlFunction ... functions) {
		JDialog win = new JDialog(this, false);
		
		win.setLocation(100, this.getHeight());
		win.setLayout(new GridLayout(0, 3));
		
		// A special "null" button
		JButton button = new JButton("]");
		button.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				try {
					builder.insert(null);
				}
				catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		});
		win.add(button);
		
		// Create buttons for all functions
		for (int i = 0; i < functions.length; i++) {
			final CamlFunction f = functions[i];

			Color color = Color.GRAY;
			
			CamlType lastType = f.camlType().getLastType();
			if (lastType.equals(CamlType.THM))
				color = Color.CYAN;
			
			if (lastType.equals(CamlType.GOAL_STATE))
				color = Color.GREEN;
			
			
			button = new JButton(f.toCommandString());
			button.setBackground(color);
			button.addActionListener(new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					try {
						builder.insert(f);
					}
					catch (Exception ex) {
						ex.printStackTrace();
					}
				}
			});
			
			win.add(button);
		}
		
		win.pack();
		win.setVisible(true);
	}
	
	
	/**
	 * Main function
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
		TermPrinterData.init();
		
//		TestGUI test = new TestGUI(new TestCamlEnvironment());
		TestGUI test = new TestGUI(new EmptyCamlEnvironment());
		CamlObjectList terms = test.getTerms();

		// Test terms
        String str1 = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Comb(Const(\"GABS\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])])),Abs(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"num\"[])),Comb(Comb(Const(\"GEQ\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\",\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])])),Var(\"x\",Tyapp(\"num\"[]))),Var(\"y\",Tyapp(\"num\"[]))))),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"z\",Tyapp(\"num\"[])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"y\",Tyapp(\"num\"[]))),Var(\"z\",Tyapp(\"num\"[]))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))))))))))))";
        String str2 = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyvar(\"B\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"y\",Tyvar(\"B\")))))))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Comb(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Var(\"x\",Tyvar(\"A\")))))))))))";
        String str3 = "Comb(Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Var(\"y\",Tyapp(\"num\"[])))";
        String str4 = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"real\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"z\",Tyapp(\"real\"[])),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"x\",Tyapp(\"num\"[])))))))))";
        String str5 = "Comb(Const(\"GABS\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])])])),Abs(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"t\",Tyapp(\"num\"[])),Comb(Comb(Const(\"GEQ\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])])),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"t\",Tyapp(\"num\"[]))))),Comb(Const(\"GABS\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])])),Abs(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"a\",Tyapp(\"num\"[])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"b\",Tyapp(\"num\"[])),Comb(Comb(Const(\"GEQ\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Var(\"f\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\",\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])])),Var(\"a\",Tyapp(\"num\"[]))),Var(\"b\",Tyapp(\"num\"[]))))),Comb(Comb(Const(\"<\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"a\",Tyapp(\"num\"[]))),Var(\"b\",Tyapp(\"num\"[])))),Var(\"t\",Tyapp(\"num\"[])))))))))))))))))";
        String str6 =  "Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"real_sub\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Comb(Const(\"real_add\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))))),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))))))))),Comb(Const(\"real_neg\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))";		Term t1 = Parser.parseTerm(str1);
		Term t2 = Parser.parseTerm(str2);
		Term t3 = Parser.parseTerm(str3);
		Term t4 = Parser.parseTerm(str4);
		Term t5 = Parser.parseTerm(str5);
		Term t6 = Parser.parseTerm(str6);

		terms.add(t1);
		terms.add(t2);
		terms.add(t3);
		terms.add(t4);
		terms.add(t5);
		terms.add(t6);

		
		// Test functions
		CamlType term = CamlType.TERM;
		CamlType thm = CamlType.THM;
		CamlType term_to_thm = CamlType.mk_function(CamlType.TERM, CamlType.THM);
		CamlType thm_to_thm = CamlType.mk_function(CamlType.THM, CamlType.THM);
		CamlType thm_to_thm_to_thm = CamlType.mk_function(CamlType.THM, thm_to_thm);
		CamlType thm_to_term = CamlType.mk_function(CamlType.THM, CamlType.TERM);
		CamlType thm_list = new CamlType.ListType(thm);
		CamlType term_list = new CamlType.ListType(term);
		CamlType thm_list_to_term_to_thm = CamlType.mk_function(thm_list, CamlType.mk_function(CamlType.TERM, CamlType.THM));
		CamlType term_list_to_thm_to_thm = CamlType.mk_function(term_list, CamlType.mk_function(CamlType.THM, CamlType.THM));
		CamlType tac = CamlType.TACTIC;
		CamlType ttac = CamlType.mk_function(thm, CamlType.TACTIC);
		CamlType thm_list_to_tac = CamlType.mk_function(thm_list, tac);
		
		
		CamlFunction ARITH_RULE = new CamlFunction("ARITH_RULE", term_to_thm);
		CamlFunction REFL = new CamlFunction("REFL", term_to_thm);
		CamlFunction ASSUME = new CamlFunction("ASSUME", term_to_thm);
		CamlFunction DISCH_ALL = new CamlFunction("DISCH_ALL", thm_to_thm);
		
		CamlFunction concl = new CamlFunction("concl", thm_to_term);
		
		CamlFunction SPEC_ALL = new CamlFunction("SPEC_ALL", thm_to_thm);
		CamlFunction GEN = new CamlFunction("GEN", CamlType.mk_function(CamlType.TERM, thm_to_thm));
		
		CamlFunction REWRITE_CONV = new CamlFunction("REWRITE_CONV", thm_list_to_term_to_thm);
		CamlFunction REWRITE_RULE = new CamlFunction("REWRITE_RULE", thm_list_to_term_to_thm);
		CamlFunction SPECL = new CamlFunction("SPECL", term_list_to_thm_to_thm);
		CamlFunction MESON = new CamlFunction("MESON", thm_list_to_term_to_thm);
		
		CamlFunction MATCH_MP = new CamlFunction("MATCH_MP", thm_to_thm_to_thm);
		
		CamlFunction TAUT = new CamlFunction("TAUT", term_to_thm);
		CamlFunction CONJ = new CamlFunction("CONJ", thm_to_thm_to_thm);

		CamlFunction STRIP_TAC = new CamlFunction("STRIP_TAC", CamlType.TACTIC);
		CamlFunction MATCH_MP_TAC = new CamlFunction("MATCH_MP_TAC", ttac);
		CamlFunction CONJ_TAC = new CamlFunction("CONJ_TAC", tac);
		CamlFunction REWRITE_TAC = new CamlFunction("REWRITE_TAC", thm_list_to_tac);
		CamlFunction ARITH_TAC = new CamlFunction("ARITH_TAC", tac);
		CamlFunction GEN_TAC = new CamlFunction("GEN_TAC", tac);
		CamlFunction DISCH_TAC = new CamlFunction("DISCH_TAC", tac);
		CamlFunction ASM_REWRITE_TAC = new CamlFunction("ASM_REWRITE_TAC", thm_list_to_tac);
		
		
		test.createFunctions(ARITH_RULE, REFL, ASSUME, DISCH_ALL, concl, 
				SPEC_ALL, GEN, SPECL, REWRITE_CONV,
				REWRITE_RULE, MESON, MATCH_MP, TAUT, CONJ,
				STRIP_TAC, MATCH_MP_TAC, CONJ_TAC,
				REWRITE_TAC, ARITH_TAC, GEN_TAC,
				DISCH_TAC, ASM_REWRITE_TAC);

		
		
		// A test theorem
		Theorem th = Theorem.mk_theorem("TEST_THM", t1);
		terms.add(th);
		
		terms.add(CONJ);
	}


}
