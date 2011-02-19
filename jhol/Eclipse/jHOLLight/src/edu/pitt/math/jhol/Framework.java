package edu.pitt.math.jhol;

import java.awt.Dimension;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.Window;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;

import javax.swing.JFrame;
import javax.swing.JOptionPane;

import bsh.Interpreter;

import com.apple.eawt.*;

public class Framework extends WindowAdapter{

	
	private HOLLightWrapper hol;
	private AboutDialog ad;
	private JFrame frame;
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
		hol.kill();
		System.exit(0);
	    }
	    System.out.println("Quit operation not confirmed; staying alive.");
	}
	
	public Framework(Interpreter interpreter) {
		
		Point lastLocation = null;
		int maxX = 500;
		int maxY = 500;

			
		Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
		maxX = screenSize.width - 50;
		maxY = screenSize.height - 50;	
		
		WindowAdapter controller = this;
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
		     frame = new JFrame()
			
		    
		    //Create buttons 
		    JButton sigIntButton = new JButton("Assume");
		    sigIntButton.setActionCommand("assume");
		    JButton genTac = new JButton("Remove  \"for all\"");
		    genTac.setActionCommand("e(GEN_TAC);;");
		    JButton conjTac = new JButton("Remove Conjuction");
		    conjTac.setActionCommand("e(CONJ_TAC);;");
		    JButton conjTac1 = new JButton("Test Button 1");
		    conjTac1.setActionCommand("test1");
		    JButton conjTac2 = new JButton("Interrupt");
		    conjTac2.setActionCommand("test2");
							       
		    //Keep track of buttons
		    List buttonList = new LinkedList();
		    buttonList.add(sigIntButton);
		    buttonList.add(genTac);
		    buttonList.add(conjTac);
		    buttonList.add(conjTac1);
		    buttonList.add(conjTac2);


		    //Console for getting input from user
		    JConsole console = new JConsole();
		    consoleTextPane = console.getViewport().getView();
		    consoleTextPane.addKeyListener( new KeyListener(){
			    invoke( name, args ) { print("Method: "+name+" invoked!");}
			    //handle other methods
			    void keyPressed(KeyEvent e){
				if  (e.getKeyCode() != KeyEvent.VK_ENTER )
				    return;
				
				//Main Loop
				List cmdList = new LinkedList();
				try {	
				    //	    do
					//{
					    //in case someone pastes more than one command into the buffer	    
					    line = readLine(bufInput);
					    cmdList.add(line);
					    //		}while(bufInput.ready());
				    while(cmdList.size() != 0){
					printHTML(global.runCommand(cmdList.removeFirst()  + "\n"));
				    }	   
				    //updateTopGoal();
				    
				} catch (IOException e) {
				    e.printStackTrace();
				}
			    }
			});

		     
		    //Method for printing to the console
		    printHTML(String html){
			while (html.indexOf("<HTML>") != -1){
			    int start = html.indexOf("<HTML>");
			    //console.print(html.substring(0, start));//Print any text that occurs before the HTML
			    int end = html.indexOf("</HTML>");
			    htmlText = html.substring(start,end+7);
			    JLabel tmpLabel = GoalPane.htmlToJLabel(htmlText);
			    consoleTextPane.insertComponent(tmpLabel);
			    html = html.substring(end+7, html.length());
			}
			console.print(html);
		    }
		    
		    //Reader for the console
		    BufferedReader bufInput = new BufferedReader(console.getIn());
		    
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
		List command = new ArrayList();
			command.add("./local.hol");
			
			es = Executors.newCachedThreadPool();
			futureHOL = es.submit(HOLLightWrapper.getHOLBuilderTask(command));
			

		    global.hol = futureHOL.get();
			
			printHTML("# ");
		    
		    
		    try{
			newprinterMLStream = new BufferedReader(new FileReader("newprinter.ml"));
			int c = newprinterMLStream.read();
			StringBuilder newprinterMLString = new StringBuilder();
			while (c != -1){
			    newprinterMLString.append((char)c);
			    c = newprinterMLStream.read();
			}

			runHOLCommands(newprinterMLString.toString());
		    }
		    catch (IOException x) {
			System.err.println(x);
		    } 
		    finally{
			if (newprinterMLStream != null)
			    newprinterMLStream.close();
		    }
		    



		    //update the theorem list
		    global.hol.updateHolTheorems();

		    sourceRelative("name.bsh");


		    test1(){
			global.runCommand("g `!x. ~(x = &1) ==> !n. (sum(0..n) (\\i. x pow i) = ((x pow (n + 1)) - &1) / (x - &1))`;;");
		    }

		    //List of theorem labels
		    String[] thmStrings = { "All", "Basic Logic", "Constructs", "Pairs", "Well Foundedness",
					    "Natural Numbers", "Lists", "Real Numbers", "Integers",
					    "Sets and Functions", "Iterated Operations", "Cartesian Powers"};

		    //Combo box to select which list of theorems to list
		    JComboBox thmCombo = new JComboBox(thmStrings);
		    JList myList = new JList ();

		    //find the matching set of theorems
		    lookupTheoremList(String name){
			if (name.equals("Real Numbers"))
			    return realNumberTheorems.toArray();
			if (name.equals("Integers"))
			    return integerTheorems.toArray();
			if (name.equals("Sets and Functions"))
			    return setAndFunctionTheorems.toArray();
			if (name.equals("Iterated Operations"))
			    return iteratedOperationTheorems.toArray();
			if(name.equals("Cartesian Powers"))
			    return cartesianPowerTheorems.toArray();
			if(name.equals("Constructs"))
			    return constructTheorems.toArray();
			if(name.equals("Pairs"))
			    return pairTheorems.toArray();
			if(name.equals("Well Foundedness"))
			    return wellfoundednessTheorems.toArray();
			if (name.equals("Natural Numbers"))
			    return naturalNumberTheorems.toArray();
			if(name.equals("Lists"))
			    return listTheorems.toArray();
			if (name.equals("All"))
			    {
				global.hol.updateHolTheorems();
				return global.hol.getTheoremList().toArray();
			    }
			if( name.equals("Basic Logic"))
			    return basicLogicTheorems.toArray();

			return null;
		    }

		    //Detect mouse clicks
		    ml = new MouseAdapter() {
			    public void mouseClicked(MouseEvent e) {
				if (e.getClickCount() == 2) {
				    global.runCommand(((String)e.getSource().getSelectedValue())+";;");
				}
			    }
			};

		    //Detect button presses
		    al  = new ActionListener() {
			    actionPerformed( event ) {
				if ( event.getSource() == thmCombo){
				    myList.setListData(lookupTheoremList(thmStrings[thmCombo.getSelectedIndex()]));
				}
			    
				if (event.getActionCommand().startsWith("e"))
				    global.runCommand(event.getActionCommand());
				
				if (event.getActionCommand().equals("test1")){
				    test1();
				}
				if(event.getActionCommand().equals("test2")){
				    try {
					conjTac2.setEnabled(false);
					kill.start();
					//	print(hol.flushOutput(false));
				    
				    } catch (IOException e) {
					return null;
				    }
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

		    console.setPreferredSize(new Dimension(700,400));

		    //START EDITORPANE
		    
		   /* helpScrollPane.setPreferredSize(new Dimension(250, 145));
		    helpScrollPane.setMinimumSize(new Dimension(10, 10));
		    */global.goalPane = new GoalPane(global.hol);
		    JScrollPane editorScrollPane = new JScrollPane(global.goalPane);

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
	    Window window = e.getWindow();
	    window.zoomItem.setEnabled(false);
	    window.minimizeItem.setEnabled(false);
	}	
	public void windowDeiconified(WindowEvent e){
	    Window window = e.getWindow();
	    window.zoomItem.setEnabled(true);
	    window.minimizeItem.setEnabled(true);
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
	
}
