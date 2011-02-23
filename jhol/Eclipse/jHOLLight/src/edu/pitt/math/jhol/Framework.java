package edu.pitt.math.jhol;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import bsh.Interpreter;
import bsh.util.JConsole;
import com.apple.eawt.*;

public class Framework extends WindowAdapter{

	
	
	private AboutDialog ad;
	private HOLFrame frame;
	private List<JButton> buttonList;
	private HOLConsole console;
	

	private GoalPane goalPane;
	
	public GoalPane getGoalPane(){
		return goalPane;
	}
	
	//DEBUG	
	boolean quitConfirmed(JFrame frame) {
	    String s1 = "Quit";
	    String s2 = "Cancel";
	    Object[] options = {s1, s2};
	    int n = JOptionPane.showOptionDialog(((JFrame)frame),
						 "Windows are still open.\nDo you really want to quit?",
						 "Quit Confirmation",
						 JOptionPane.YES_NO_OPTION,
						 JOptionPane.QUESTION_MESSAGE,
						 null,
						 options,
						 s1);
	    if (n == JOptionPane.YES_OPTION) {
		return true;
	    } else {
		return false;
	    }
	}
	
	
	
	//This method must be evoked from the event-dispatching thread.
	public void quit(JFrame frame) {
	    if (quitConfirmed(frame)) {
		System.out.println("Quitting.");
		console.kill();
		System.exit(0);
	    }
	    System.out.println("Quit operation not confirmed; staying alive.");
	}
	
	public Framework(Interpreter interpreter) {
		
		
		
		    boolean IS_A_MAC = System.getProperty("os.name").equals("Mac OS X");
							       
		  //begin MacOS stuff
		    if (IS_A_MAC){
			AboutHandler aboutHandler = new AboutHandler() {
				public void handleAbout(com.apple.eawt.AppEvent.AboutEvent event) {
				    (ad).setVisible(true);
				}
			    };
								   
			PreferencesHandler preferencesHandler = new PreferencesHandler(){
				public void handlePreferences(com.apple.eawt.AppEvent.PreferencesEvent e) {
				    //what to do on flower-,
				}
			    };
			    
			    QuitHandler quitHandler = new QuitHandler(){
			    	public void handleQuitRequestWith(AppEvent.QuitEvent e,
		                    QuitResponse response){
			    		
			    	}
			    };
								   
			Application macOSApplication = Application.getApplication() ;
			macOSApplication.setAboutHandler(aboutHandler);
			macOSApplication.setPreferencesHandler(preferencesHandler);
			macOSApplication.setQuitHandler(quitHandler);
		    }
		    //end MacOS stuff

		    ad = new AboutDialog();

		    //Create frame
		     frame = new HOLFrame();
			
		     frame.addWindowListener(this);
		    //Create buttons 
		    JButton sigIntButton = new JButton("Assume");
		    sigIntButton.setActionCommand("assume");
		    JButton genTac = new JButton("Remove  \"for all\"");
		    genTac.setActionCommand("e(GEN_TAC);;");
		    JButton conjTac = new JButton("Remove Conjuction");
		    conjTac.setActionCommand("e(CONJ_TAC);;");
		    JButton conjTac1 = new JButton("Test Button 1");
		    conjTac1.setActionCommand("test1");
		    final JButton conjTac2 = new JButton("Interrupt");
		    conjTac2.setActionCommand("test2");
							       
		    //Keep track of buttons
		    buttonList = new LinkedList<JButton>();
		    buttonList.add(sigIntButton);
		    buttonList.add(genTac);
		    buttonList.add(conjTac);
		    buttonList.add(conjTac1);
		    buttonList.add(conjTac2);


		    
		     
		     
		    
		    
		    
		    /*//For creating panes
		    JTextPane createEditorPane() {
			JTextPane editorPane = new JTextPane(new DefaultStyledDocument());
			editorPane.setEditable(false);
			return editorPane;
		    }*/
		    
		    //Panes for displaying different output
		    
		    /*helpPane = createEditorPane();
		    JScrollPane helpScrollPane = new JScrollPane(helpPane);
		*/

		    

		    //start a new hol process
		
			String user = "joepleso";
			String server = "weyl";
			ExecutorService es = Executors.newCachedThreadPool();
			Future<HOLLightWrapper> futureHOL = es.submit(HOLLightWrapper.getHOLBuilderTask(user,server,interpreter));
			

			HOLLightWrapper tmp2 = null;
		    final HOLLightWrapper hol;
			try {
				 tmp2 = futureHOL.get();
			} catch (InterruptedException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (ExecutionException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			hol = tmp2;
			
			//Console for getting input from user
		     console = new HOLConsole(hol);
		    
		    BufferedReader newprinterMLStream = null;
			try{
			newprinterMLStream = new BufferedReader(new FileReader("newprinter.ml"));
			int c = newprinterMLStream.read();
			StringBuilder newprinterMLString = new StringBuilder();
			while (c != -1){
			    newprinterMLString.append((char)c);
			    c = newprinterMLStream.read();
			}

			hol.runHOLCommands(newprinterMLString.toString());
		    }
		    catch (IOException x) {
			System.err.println(x);
		    } 
		    finally{
			if (newprinterMLStream != null)
				try {
					newprinterMLStream.close();
				} catch (IOException e1) {
					
					e1.printStackTrace();
				}
		    }
		    



		    //update the theorem list
		    hol.updateHolTheorems();

		

		  

		    

		    

		    //List of theorem labels
		    final String[] thmStrings = { "All", "Basic Logic", "Constructs", "Pairs", "Well Foundedness",
					    "Natural Numbers", "Lists", "Real Numbers", "Integers",
					    "Sets and Functions", "Iterated Operations", "Cartesian Powers"};

		    //Combo box to select which list of theorems to list
		    final JComboBox thmCombo = new JComboBox(thmStrings);
		    final JList myList = new JList ();

		    

		    //Detect mouse clicks
		    MouseAdapter ml = new MouseAdapter() {
			    public void mouseClicked(MouseEvent e) {
				if (e.getClickCount() == 2) {
				    hol.runCommand(((String)((JList) e.getSource()).getSelectedValue())+";;");
				}
			    }
			};

		    //Detect button presses
		    ActionListener al = new ActionListener() {
			    public void actionPerformed( ActionEvent event ) {
				if ( event.getSource() == thmCombo){
				    myList.setListData(lookupTheoremList(thmStrings[thmCombo.getSelectedIndex()]));
				}
			    
				if (event.getActionCommand().startsWith("e"))
				   hol.runCommand(event.getActionCommand());
				
				if (event.getActionCommand().equals("test1")){
				    test1();
				}
				if(event.getActionCommand().equals("test2")){
				    conjTac2.setEnabled(false);
					hol.interrupt();
					//	print(hol.flushOutput(false));
				}
			    }
			};

		    /*
		      SPEC  copy paste
		      INDUCT_TAC
		      ALL_TAC
		      UNDISCH_TAC
		      asm ONCE PURE REWRITE_TAC
		      /SIMP_TAC
		      let_tac
		      asm meson tac
		      highlight delete comma rewrite tac pair eq
		      abbrev tac highlight type
		      sexpand tac highlight
		      mp_tac thm
		      assume_tac

		      rewritetac real arith 1+1 highlight type 2
		      ap thm tac
		      ap term tac
		      gsym
		      sqrt pos lt

		    */

		    JPanel toolbar = new JPanel();

		  
		    //START EDITORPANE
		    
		   /* helpScrollPane.setPreferredSize(new Dimension(250, 145));
		    helpScrollPane.setMinimumSize(new Dimension(10, 10));
		    */
		    goalPane = new GoalPane(hol);
		    JScrollPane editorScrollPane = new JScrollPane(goalPane);

		    editorScrollPane.setPreferredSize(new Dimension(250, 145));
		    editorScrollPane.setMinimumSize(new Dimension(10, 10));




		    //Put the editor pane and the text pane in a split pane.
		    JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
							  editorScrollPane,
							  console);
		    splitPane.setOneTouchExpandable(true);
		    splitPane.setResizeWeight(0.5);


		    for (JButton jb: buttonList){
			jb.addActionListener(al);
			toolbar.add(jb);
		    }

		    conjTac2.setEnabled(false);


		    myList.setLayoutOrientation(JList.VERTICAL);
		    JScrollPane myScroll = new JScrollPane(myList);
		    myList.addMouseListener(ml);


		    toolbar.add(thmCombo);
		    //END EDITORPANE


		    thmCombo.setSelectedIndex(0);
		    thmCombo.addActionListener(al);

		    myList.setListData(lookupTheoremList(thmStrings[thmCombo.getSelectedIndex()]));

		    frame.getContentPane().add(toolbar,BorderLayout.NORTH);
		    frame.getContentPane().add(splitPane,BorderLayout.WEST);
		    frame.getContentPane().add(myScroll,BorderLayout.CENTER);
		    frame.setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE);

		    //Display the window.
		    frame.pack();

		    frame.setVisible(true);

		    //tmp2();//DEBUG

		
		
		
		
		
	    }
	
	
	public void windowStateChanged(WindowEvent e){
	    
	}	

        public void windowClosed(WindowEvent e) {
	   
	}
	public void windowClosing(WindowEvent e ){
	   
	}

	public void windowIconified(WindowEvent e){
	    HOLFrame window = (HOLFrame) e.getWindow();
	    window.getZoomItem().setEnabled(false);
	    window.getMinimizeItem().setEnabled(false);
	}	
	public void windowDeiconified(WindowEvent e){
	    HOLFrame window = (HOLFrame) e.getWindow();
	    window.getZoomItem().setEnabled(true);
	    window.getMinimizeItem().setEnabled(true);
	}	
	    		
	/*	void makeNewWindow() {
		frame = getNewMyFrame(this);
		numWindows++;
		System.out.println("Number of windows: " + numWindows);
	    
		if (lastLocation != null) {
		//Move the window over and down 40 pixels.
		lastLocation.translate(40, 40);
		if ((lastLocation.x > maxX) || (lastLocation.y > maxY)) {
		lastLocation.setLocation(0, 0);
		}
		frame.setLocation(lastLocation);
		} else {
		lastLocation = frame.getLocation();
		}
	    
		System.out.println("Frame location: " + lastLocation);
		frame.setVisible(true);
		}*/
	
	
    void test1(){
		hol.runCommand("g `!x. ~(x = &1) ==> !n. (sum(0..n) (\\i. x pow i) = ((x pow (n + 1)) - &1) / (x - &1))`;;");
	    }
  //find the matching set of theorems
    private String[] lookupTheoremList(String name){
	if (name.equals("Real Numbers"))
	    return  Database.realNumberTheorems.toArray(new String[0]);
	if (name.equals("Integers"))
	    return (String[]) Database.integerTheorems.toArray(new String[0]);
	if (name.equals("Sets and Functions"))
	    return (String[]) Database.setAndFunctionTheorems.toArray(new String[0]);
	if (name.equals("Iterated Operations"))
	    return (String[]) Database.iteratedOperationTheorems.toArray(new String[0]);
	if(name.equals("Cartesian Powers"))
	    return (String[]) Database.cartesianPowerTheorems.toArray(new String[0]);
	if(name.equals("Constructs"))
	    return (String[]) Database.constructTheorems.toArray(new String[0]);
	if(name.equals("Pairs"))
	    return (String[]) Database.pairTheorems.toArray(new String[0]);
	if(name.equals("Well Foundedness"))
	    return (String[]) Database.wellfoundednessTheorems.toArray(new String[0]);
	if (name.equals("Natural Numbers"))
	    return (String[]) Database.naturalNumberTheorems.toArray(new String[0]);
	if(name.equals("Lists"))
	    return (String[]) Database.listTheorems.toArray(new String[0]);
	if (name.equals("All"))
	    {
		hol.updateHolTheorems();
		return (String[]) hol.getTheoremList().toArray(new String[0]);
	    }
	if( name.equals("Basic Logic"))
	    return (String[]) Database.basicLogicTheorems.toArray(new String[0]);

	return null;
    }
}
