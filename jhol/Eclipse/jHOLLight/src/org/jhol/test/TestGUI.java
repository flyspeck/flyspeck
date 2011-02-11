package org.jhol.test;

import java.awt.Dimension;
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

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlFunction;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;
import org.jhol.core.lexer.TermParser;

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
	
	private ExpressionBuilder builder;
	
	/**
	 * Constructor
	 */
	public TestGUI(CamlEnvironment caml) {
		this.caml = caml;
		
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setPreferredSize(new Dimension(800, 600));
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
		dialog.setLocation(800, 100);
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
		termsTable.getSelectionModel().addListSelectionListener(new ListSelectionListener() {
			@Override
			public void valueChanged(ListSelectionEvent e) {
				try {
					int index = termsTable.getSelectedRow();
					if (index < 0)
						return;
					
					CamlObject obj = terms.get(index);
					builder.insert(obj);
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
		add(termField);
	}
	

	/**
	 * Action listener
	 */
	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == termField) {
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
		
		win.setLocation(800, 400);
		win.setLayout(new BoxLayout(win.getContentPane(), BoxLayout.PAGE_AXIS));
		
		for (int i = 0; i < functions.length; i++) {
			final CamlFunction f = functions[i];
			JButton button = new JButton(f.toCommandString());
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
		TestGUI test = new TestGUI(new TestCamlEnvironment());
//		TestGUI test = new TestGUI(new EmptyCamlEnvironment());
		CamlObjectList terms = test.getTerms();

		// Test terms
		String str1 = "Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"hull\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])])])),Const(\"convex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))";
		String str2 = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyvar(\"B\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"y\",Tyvar(\"B\")))))))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Comb(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Var(\"x\",Tyvar(\"A\")))))))))))";
		String str3 = "Comb(Comb(Var(\"f\",Tyapp(\"fun\"[Tyvar(\"?961032\"),Tyapp(\"fun\"[Tyvar(\"?961031\"),Tyvar(\"?961030\")])])),Comb(Var(\"g\",Tyapp(\"fun\"[Tyvar(\"?961033\"),Tyvar(\"?961032\")])),Var(\"x\",Tyvar(\"?961033\")))),Var(\"y\",Tyvar(\"?961031\")))";
		Term t1 = TermParser.parseTerm(str1);
		Term t2 = TermParser.parseTerm(str2);
		Term t3 = TermParser.parseTerm(str3);

		terms.add(t1);
		terms.add(t2);
		terms.add(t3);

		
		// Test functions
		CamlType term_to_thm = CamlType.mk_function(CamlType.TERM, CamlType.THM);
		CamlType thm_to_thm = CamlType.mk_function(CamlType.THM, CamlType.THM);
		CamlType thm_to_term = CamlType.mk_function(CamlType.THM, CamlType.TERM);
		
		CamlFunction ARITH_RULE = new CamlFunction("ARITH_RULE", term_to_thm);
		CamlFunction REFL = new CamlFunction("REFL", term_to_thm);
		
		CamlFunction concl = new CamlFunction("concl", thm_to_term);
		
		CamlFunction SPEC_ALL = new CamlFunction("SPEC_ALL", thm_to_thm);
		CamlFunction GEN = new CamlFunction("GEN", CamlType.mk_function(CamlType.TERM, thm_to_thm));
		
		
		test.createFunctions(ARITH_RULE, REFL, concl, SPEC_ALL, GEN);

		
		
		// A test theorem
		Theorem th = Theorem.mk_theorem("TEST_THM", t1);
		terms.add(th);
	}


}
