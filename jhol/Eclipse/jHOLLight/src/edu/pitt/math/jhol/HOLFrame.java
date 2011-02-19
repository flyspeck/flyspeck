package edu.pitt.math.jhol;

import java.awt.Toolkit;
import java.awt.event.WindowAdapter;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;



public class HOLFrame extends JFrame {

	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private WindowAdapter framework;
	public HOLFrame(WindowAdapter controller){
	    //set name to JHOL DEBUG//
	    framework = controller;
	    addWindowListener(framework);
	    
	   
	    HOLHelp holHelpDialog = new HOLHelp(this);

	    JMenu menu = new JMenu("File");
	    JMenu helpMenu = new JMenu("Help");
	    JMenu windowMenu = new JMenu("Window");
	    
	    JMenuItem item = null;
	    
	    //HOL Light Commands
	    item = new JMenuItem("HOL Light Commands");
	    //	    item.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_M,
	    //						       Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));		
	    getNewHOLCommandHelpListener(child){
		return new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			//System.out.println("Minimize request");
			//child.setState ( Frame.ICONIFIED );;
			child.popupHOLHelp();
		    }
		};
	    }	
	    item.addActionListener(getNewHOLCommandHelpListener(holHelpDialog));
	    //	    JMenuItem minimizeItem = item;	
	    helpMenu.add(item);


	    //minimize
	    item = new JMenuItem("Minimize");
	    item.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_M,
						       Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));		
	    getNewMinimizeListener(child){
		return new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			System.out.println("Minimize request");
			child.setState ( Frame.ICONIFIED );;
		    }
		};
	    }	
	    item.addActionListener(getNewMinimizeListener(this));
	    JMenuItem minimizeItem = item;	
	    windowMenu.add(item);
	    
	    //Zoom
	    item = new JMenuItem("Zoom");
	    item.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Z,
						       6));	//6 is ctrl-meta mask
	    getNewZoomListener(child){
		return new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			System.out.println("Zoom request");
			if ((child.getExtendedState() & Frame.MAXIMIZED_BOTH) == Frame.MAXIMIZED_BOTH)
			    child.setExtendedState(Frame.MAXIMIZED_BOTH ^ child.getExtendedState());
			else
			    child.setExtendedState(Frame.MAXIMIZED_BOTH | child.getExtendedState());		    
		    }
		};
	    }	
	    item.addActionListener(getNewZoomListener(this));
	    JMenuItem zoomItem = item;
	    windowMenu.add(item);
	    
	    //new
	    /*	    item = new JMenuItem("New Window");
		    item.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N,
		    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));		
		    item.addActionListener(new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
		    System.out.println("New window");
		    framework.makeNewWindow();
		    }
		    });
		    menu.add(item);*/
	    
	    //close
	    /*  item = new JMenuItem("Close");
		item.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_W,
		Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
		item.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		System.out.println("Close window");
		super.setVisible(false);
		super.dispose();
		}
		});
		menu.add(item);
	    */
	    /*		//quit
			item = new JMenuItem("Quit");
			item.setMnemonic(KeyEvent.VK_Q);
			getNewQuitListener(child){
			return new ActionListener() {
			public void actionPerformed(ActionEvent e) {
			System.out.println("Quit request");
			framework.quit(child);
			}
			};
			}*/
	    
	    //	item.addActionListener(getNewQuitListener(this));
	    //	menu.add(item);
	    
	    JMenuBar menuBar = new JMenuBar();
	    menuBar.add(menu);
	    menuBar.add(windowMenu);
	    menuBar.add(helpMenu);
	    setJMenuBar(menuBar);
	}
	
	
}
