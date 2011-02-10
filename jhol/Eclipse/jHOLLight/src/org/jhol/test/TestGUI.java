package org.jhol.test;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.Term;
import org.jhol.core.lexer.TermParser;

/**
 * Test GUI
 * @author Alexey
 *
 */
@SuppressWarnings("serial")
public class TestGUI extends JFrame implements ActionListener {
	private CamlEnvironment caml;
	
	private TermList terms;
	private JTextField termField;
	
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
		
	}
	
	
	/**
	 * Initializes the user interface
	 */
	private void initInterface() {
		// A table of terms
		terms = new TermList();
		JTable termsTable = new JTable(terms);
		
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
				terms.addTerm(term);
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		}
	}

	
	/**
	 * Returns the list of terms
	 */
	public TermList getTerms() {
		return terms;
	}
	
	
	/**
	 * Main function
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
		TestGUI test = new TestGUI(null);
		TermList terms = test.getTerms();
		
		String str1 = "Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"hull\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])])])),Const(\"convex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))";
		String str2 = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyvar(\"B\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"y\",Tyvar(\"B\")))))))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Comb(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Var(\"x\",Tyvar(\"A\")))))))))))";
		String str3 = "Comb(Comb(Var(\"f\",Tyapp(\"fun\"[Tyvar(\"?961032\"),Tyapp(\"fun\"[Tyvar(\"?961031\"),Tyvar(\"?961030\")])])),Comb(Var(\"g\",Tyapp(\"fun\"[Tyvar(\"?961033\"),Tyvar(\"?961032\")])),Var(\"x\",Tyvar(\"?961033\")))),Var(\"y\",Tyvar(\"?961031\")))";
		Term t1 = TermParser.parseTerm(str1);
		Term t2 = TermParser.parseTerm(str2);
		Term t3 = TermParser.parseTerm(str3);
		
		terms.addTerm(t1);
		terms.addTerm(t2);
		terms.addTerm(t3);
	}


}
