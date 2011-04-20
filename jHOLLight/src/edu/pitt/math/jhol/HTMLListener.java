package edu.pitt.math.jhol;

import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.SwingUtilities;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkListener;

public class HTMLListener implements HyperlinkListener{
	private JFrame f;
	private JScrollPane sp;
	public HTMLListener(JFrame f, JScrollPane sp){
		this.f = f;
		this.sp = sp;
	 
		    
		    }
		
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
			pane.setText(Utilities.readFile("HTML/"+e.getDescription()));
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
}
