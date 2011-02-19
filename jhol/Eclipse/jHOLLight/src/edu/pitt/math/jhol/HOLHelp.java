package edu.pitt.math.jhol;

import java.util.regex.Pattern;

import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JTextField;

import org.apache.commons.collections.CollectionUtils;
import org.apache.commons.collections.Predicate;

public class HOLHelp {
	private JTextField filterText;
	private JList list;
	void newFilter(){
		final Pattern p = null;
		try{
		    p = java.util.regex.Pattern.compile(filterText.getText());
		}		
		catch (java.util.regex.PatternSyntaxException e) {

	        }
		if (p == null)
		    return;
		
		Predicate pred = new Predicate(){
			public boolean evaluate (Object input){
			    return ((Pattern) p).matcher((CharSequence) input).find();
			}
		    };

			

		list.setListData(CollectionUtils.select(HOL_COMMANDS,pred).toArray());
	    }
	
	
	
	HOLHelp(JFrame parent){
		   

	    
	    
	    getHTMLListener(JFrame f, JScrollPane sp){
		return new  HyperlinkListener() {
	 
		    public void hyperlinkUpdate(HyperlinkEvent e) {
			if (e.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
			    JEditorPane pane = (JEditorPane) e.getSource();
			    // if (e instanceof HTMLFrameHyperlinkEvent) {
			    //HTMLFrameHyperlinkEvent  evt = (HTMLFrameHyperlinkEvent)e;
			    //       HTMLDocument doc = (HTMLDocument)pane.getDocument();
			    //       doc.processHTMLFrameHyperlinkEvent(evt);
			    //   } else {
			    try {
				//pane.setPage(e.getURL());
				pane.setText(readFile("HTML/"+e.getDescription()));
				//	sp.getViewport().setViewPosition(new Point());
		

				    SwingUtilities.invokeLater(new Runnable()
					{
					    public void run()
					    {
						sp.getVerticalScrollBar().setValue(0);   
						sp.getHorizontalScrollBar().setValue(0);
					    }           
					});       

				f.setTitle(e.getDescription().split("\\.")[0]);
			    } catch (Throwable t) {
				t.printStackTrace();
			    }
			}
		    }
		};
	    }
	    


	    //Detect mouse clicks
	    MouseListener ml = new MouseAdapter() {
		    public void mouseClicked(MouseEvent e) {
			if (e.getClickCount() == 2) {
			  
			    String filename = "HTML/" + ((String)e.getSource().getSelectedValue())
				+ ".html";
			    String epText = readFile(filename);
			    JEditorPane ep = new JEditorPane("text/html",
							     epText);
			     ep.setEditable(false);
		
			     JScrollPane sp = new JScrollPane(ep);
			     JFrame helpFrame = new JFrame(((String)e.getSource().getSelectedValue()));
			     helpFrame.getContentPane().add(sp);
			     ep.addHyperlinkListener(getHTMLListener(helpFrame,sp));
			     helpFrame.pack();
			     helpFrame.show();
			}
		    }
		};

	    JDialog d = new JDialog (parent, "HOL Commands Help", false);
	    cp  = d.getContentPane();

	    JList list = new JList ();
	    list.setListData( HOL_COMMANDS.toArray());
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

	    popupHOLHelp(){
		filterText.setText("");
		d.show();
	    }

	    cp.add(filterText, BorderLayout.NORTH);
	    d.pack();
	    return this;    
	    
	}




}
