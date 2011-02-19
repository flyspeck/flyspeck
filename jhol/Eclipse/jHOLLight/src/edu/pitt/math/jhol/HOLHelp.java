package edu.pitt.math.jhol;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.regex.Pattern;

import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import org.apache.commons.collections.CollectionUtils;
import org.apache.commons.collections.Predicate;

public class HOLHelp {
	private JTextField filterText;
	private JList list;
	private JDialog d;
	void newFilter(){
		Pattern p = null;
		try{
		    p = java.util.regex.Pattern.compile(filterText.getText());
		}		
		catch (java.util.regex.PatternSyntaxException e) {

	        }
		if (p == null)
		    return;
		final Pattern p2 = p;
		Predicate pred = new Predicate(){
			public boolean evaluate (Object input){
			    return ((Pattern) p2).matcher((CharSequence) input).find();
			}
		    };

			

		list.setListData(CollectionUtils.select(Database.HOL_COMMANDS,pred).toArray());
	    }
	
	
	
	HOLHelp(JFrame parent){
		   

	    //Detect mouse clicks
	    MouseListener ml = new MouseAdapter() {
		    public void mouseClicked(MouseEvent e) {
			if (e.getClickCount() == 2) {
			  
			    String filename = "HTML/" + ((String)((JList) e.getSource()).getSelectedValue())
				+ ".html";
			    String epText = Utilities.readFile(filename);
			    JEditorPane ep = new JEditorPane("text/html",
							     epText);
			     ep.setEditable(false);
		
			     JScrollPane sp = new JScrollPane(ep);
			     JFrame helpFrame = new JFrame(((String)((JList) e.getSource()).getSelectedValue()));
			     helpFrame.getContentPane().add(sp);
			     ep.addHyperlinkListener(new HTMLListener(helpFrame,sp));
			     helpFrame.pack();
			     helpFrame.setVisible(true);
			}
		    }
		};

	     d = new JDialog (parent, "HOL Commands Help", false);
	    Container cp = d.getContentPane();

	    JList list = new JList ();
	    list.setListData( Database.HOL_COMMANDS_STRING);
	    JScrollPane scrollPane = new JScrollPane(list);
	    list.addMouseListener(ml);
	    
	    //Add the scroll pane to this panel.
	    cp.add(scrollPane,BorderLayout.CENTER);
	      
	    filterText = new JTextField();
	    //Whenever filterText changes, invoke newFilter.
	    filterText.getDocument().addDocumentListener(
							 new DocumentListener() {
							     public void changedUpdate(DocumentEvent e) {
								 newFilter();
							     }
							     public void insertUpdate(DocumentEvent e) {
								 newFilter();
							     }
							     public void removeUpdate(DocumentEvent e) {
								 newFilter();
							     }
							 });

	    

	    cp.add(filterText, BorderLayout.NORTH);
	    d.pack();
	    
	    
	}

	public void popupHOLHelp(){
		filterText.setText("");
		d.setVisible(true);
	    }


}
