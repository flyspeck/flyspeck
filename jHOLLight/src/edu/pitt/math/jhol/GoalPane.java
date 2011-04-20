package edu.pitt.math.jhol;

import javax.swing.JLabel;
import javax.swing.JTextPane;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.StyledDocument;


public class GoalPane extends JTextPane{

	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private HOLLightWrapper hol;

	public GoalPane(HOLLightWrapper hol) {
		super(new DefaultStyledDocument());
		setEditable(false);
		this.hol = hol;
	}
	
	public void updateTopGoal() {

		JTextPane text = this;
		text.setText("");
		StyledDocument doc = text.getStyledDocument();

		// Print "Goal: "
		String htmlString = getHTMLHeader("") + "<b>Goal: </b>"
				+ getHTMLFooter();
		JLabel label = htmlToJLabel(htmlString);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print top_goal
		String junk = hol.runCommand("(snd o top_goal)();;");
		int junkInt = junk.indexOf("<HTML>");// DEBUG all html tag tests should
												// be case insensitive
		if (junkInt == -1)
			return;
		int junkEnd = junk.indexOf("</HTML>") + 7;
		junk = junk.substring(junkInt, junkEnd);
		label = htmlToJLabel(junk);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print "Assumptions: "
		htmlString = getHTMLHeader("") + "<b>Assumption(s): </b>"
				+ getHTMLFooter();
		label = htmlToJLabel(htmlString);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print the assumptions
		junk = hol.runCommand("List.iter (fun x,y ->( ((fun ()->"
				+ "(print_string \"\\n\")) o  (fun () ->"
				+ "(((print_qterm o  concl) y)))) o print_string) (\"\""
				+ "))   ((fst o top_realgoal)());;");
		while (junk.indexOf("<HTML>") != -1) {
			junkInt = junk.indexOf("<HTML>");
			junkEnd = junk.indexOf("</HTML>") + 7;
			label = htmlToJLabel(junk.substring(junkInt, junkEnd));
			junk = junk.substring(junkEnd, junk.length());
			text.insertComponent(label);
			try {
				doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
			} catch (BadLocationException e) {

				e.printStackTrace();
			}
			text.setCaretPosition(doc.getLength());
		}
	}
	


	public void beginTopGoal() {

		updateTopGoal();
	}

	

	static JLabel htmlToJLabel(String htmlText) {
		return new JLabel(htmlText, JLabel.LEFT);
	}

	static String getHTMLHeader(String title) {
		if (title == null)
			title = "";
		return "<HTML><HEAD><TITLE>" + title + "</TITLE></HEAD><BODY>";
	}

	static String getHTMLFooter() {
		return "</BODY></HTML>";
	}


	
	


	
	
}
