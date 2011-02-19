package edu.pitt.math.jhol;

import java.awt.BorderLayout;

import javax.swing.ImageIcon;
import javax.swing.JDialog;
import javax.swing.JLabel;
import java.awt.Dialog;


public class AboutDialog extends JDialog {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	AboutDialog(){
		super();
		setTitle("");
		setLayout(new BorderLayout());

		ImageIcon icon = new ImageIcon("applet.png",
					       "HAL-9000 icon");

	        //Create the first label.
	        JLabel jName = new JLabel("<html><center><font size=\"4\"><b>About JHOL</b></font><br>By Joe Pleso</center></html>",
					  icon,
					  JLabel.CENTER);
	        //Set the position of its text, relative to its icon:
	        jName.setVerticalTextPosition(JLabel.BOTTOM);
	        jName.setHorizontalTextPosition(JLabel.CENTER);
		
	       	add(jName,BorderLayout.CENTER);
		
		setDefaultCloseOperation(HIDE_ON_CLOSE);
		setModalityType(Dialog.ModalityType.MODELESS);
		setResizable(false);
		setSize(280, 220);
		
	}
}
