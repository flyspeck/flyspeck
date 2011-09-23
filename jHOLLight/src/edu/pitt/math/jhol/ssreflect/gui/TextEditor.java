package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.util.ArrayList;

import javax.swing.AbstractAction;
import javax.swing.ActionMap;
import javax.swing.InputMap;
import javax.swing.JTextPane;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.AbstractDocument;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DocumentFilter;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyledDocument;
import javax.swing.text.StyleConstants.ColorConstants;

import edu.pitt.math.jhol.ssreflect.parser.Highlighter;
import edu.pitt.math.jhol.ssreflect.parser.Interpreter;

/**
 * A component for editing scripts
 */
@SuppressWarnings("serial")
public class TextEditor extends JTextPane implements DocumentListener {
	// A script interpreter
	private final Interpreter interpreter;
	
	// Highlights the text
	private final Highlighter highlighter;
	
	// Actions
    private static final String PERIOD_ACTION = "PERIOD";
    private static final String INSERT_PERIOD_ACTION = "INSERT_PERIOD";
    private static final String REVERT_ONE_ACTION = "REVERT_ONE";
    private static final String REVERT_ACTION = "REVERT";
    
    // True if the initial text is modified
    private boolean modifiedFlag;
    
    // True when new text is initialized
    private boolean initFlag;
    
    // Position of the first writable character
    private int writePosition;
    
    
    /**
     * Listener for all events in the text editor 
     */
    public interface Listener {
    	public void modified(boolean modifiedFlag);
    }
    
    // All listeners
    private final ArrayList<Listener> listeners = new ArrayList<Listener>();
    
    
	/**
	 * Constructor
	 */
	public TextEditor(Interpreter interpreter) {
		this.interpreter = interpreter;
		this.highlighter = new Highlighter();
		this.modifiedFlag = false;
		
		this.writePosition = 0;
		
		StyledDocument doc = getStyledDocument();
		
		// doc must be isntance of AbstractDocument
		AbstractDocument adoc = (AbstractDocument) doc;
		adoc.setDocumentFilter(new WritableFilter());
		
		// Initialize the text area event listeners
        doc.addDocumentListener(this);
        
        InputMap im = getInputMap();
        ActionMap am = getActionMap();
        
        // .
        KeyStroke key = KeyStroke.getKeyStroke('.');
        im.put(key, PERIOD_ACTION);
        am.put(PERIOD_ACTION, new PeriodAction());

        // ALT + .
        key = KeyStroke.getKeyStroke(KeyEvent.VK_PERIOD, InputEvent.ALT_DOWN_MASK);
        im.put(key, INSERT_PERIOD_ACTION);
        am.put(INSERT_PERIOD_ACTION, new InsertPeriodAction());

        
        // Ctrl + Z
        key = KeyStroke.getKeyStroke(KeyEvent.VK_Z, InputEvent.CTRL_DOWN_MASK);
        im.put(key, REVERT_ONE_ACTION);
        am.put(REVERT_ONE_ACTION, new RevertOneAction());

        // Ctrl + ENTER
        key = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, InputEvent.CTRL_DOWN_MASK);
        im.put(key, REVERT_ACTION);
        am.put(REVERT_ACTION, new RevertAction());
	}
	
	
	/**
	 * Adds the given listener
	 */
	public void addListener(Listener listener) {
		if (listener != null)
			listeners.add(listener);
	}
	
	
	/**
	 * Clears the editor and sets the new text
	 */
	public void initText(String text) {
		this.writePosition = 0;
		this.initFlag = true;
		
		// Set the document initial text
		if (text != null) {
			setText(text);
			highlight(0, getDocument().getLength());
		}
		
		this.modifiedFlag = false;
		this.initFlag = false;
		notifyModified();
	}
	
	
	/**
	 * Notifies listeners that the text has been modified
	 */
	private void notifyModified() {
		for (Listener listener : listeners) {
			listener.modified(modifiedFlag);
		}
	}
	
	
	/**
	 * Returns true if the initial text is modified
	 */
	public boolean isModified() {
		return modifiedFlag;
	}
	
	
	/**
	 * Sets the modification flag
	 */
	public void setModified(boolean modifiedFlag) {
		this.modifiedFlag = modifiedFlag;
		notifyModified();
	}

	
	/**
	 * Converts the given style into a set of attributes
	 */
	private SimpleAttributeSet styleToAttributes(Highlighter.Style style) {
		SimpleAttributeSet attrs = new SimpleAttributeSet();

		// Bold
		attrs.addAttribute(ColorConstants.Bold, style.isBold());
		
		// Italic
		attrs.addAttribute(ColorConstants.Italic, style.isItalic());

		// Color
		attrs.addAttribute(ColorConstants.Foreground, new Color(style.getColor()));
   		
   		return attrs;
	}
	
	
	/**
	 * Highlights the text in the interval [start, end)
	 */
	private void highlight(int start, int end) {
		if (end <= start)
			return;
		
		try {
			String text = getText(start, end - start);
			ArrayList<Highlighter.Segment> segments = highlighter.highlight(text);
			StyledDocument doc = getStyledDocument();

			for (int i = 0; i < segments.size(); i++) {
				Highlighter.Segment s = segments.get(i);
				AttributeSet attrs = styleToAttributes(s.style);

				doc.setCharacterAttributes(start + s.start, s.length, attrs, false);
			}
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Highlights all editable text
	 */
	private void highlightAll() {
		highlight(writePosition, getDocument().getLength());
	}
	

	/**
	 * Changes the locked text
	 * @param newWritePosition
	 */
	private void changeWritePosition(int newWritePosition) {
		if (newWritePosition < 0)
			newWritePosition = 0;
		
		if (newWritePosition == writePosition)
			return;

		SimpleAttributeSet attrs = new SimpleAttributeSet();
		
		if (newWritePosition > writePosition) {
    		attrs.addAttribute(ColorConstants.Background, Color.CYAN);
    		getStyledDocument().setCharacterAttributes(writePosition, 
    				newWritePosition - writePosition, attrs, false);
		}
		else {
    		attrs.addAttribute(ColorConstants.Background, Color.WHITE);
    		getStyledDocument().setCharacterAttributes(newWritePosition, 
    				writePosition - newWritePosition, attrs, false);
		}
		
		writePosition = newWritePosition;
	}
	
	
	/**
	 * Filter for making some parts of the document uneditable
	 */
	private class WritableFilter extends DocumentFilter {
		final SimpleAttributeSet simpleAttrs;
		
		public WritableFilter() {
			simpleAttrs = new SimpleAttributeSet();
			simpleAttrs.addAttribute(ColorConstants.Background, Color.WHITE);
		}

		public void remove(FilterBypass fb, int offset, int length)
				throws BadLocationException {
			if (offset >= writePosition)
				fb.remove(offset, length);
		}

		public void insertString(FilterBypass fb, int offset, String string,
				AttributeSet attr) throws BadLocationException {
			if (offset >= writePosition)
				fb.insertString(offset, string, simpleAttrs);
		}

		public void replace(FilterBypass fb, int offset, int length,
				String text, AttributeSet attrs) throws BadLocationException {
			if (offset >= writePosition)
				fb.replace(offset, length, text, simpleAttrs);
		}

	}
	
	
	// Listener methods
    public void changedUpdate(DocumentEvent ev) {
    }
    
    public void removeUpdate(DocumentEvent ev) {
    	if (!initFlag) {
    		modifiedFlag = true;
    	
    		SwingUtilities.invokeLater(new Runnable() {
    			@Override
    			public void run() {
    				// FIXME: a better solution is required
    				highlightAll();
    				notifyModified();
    			}
    		});
    	}
    }
    
    public void insertUpdate(DocumentEvent ev) {
    	if (!initFlag) {
    		modifiedFlag = true;
    	
    		SwingUtilities.invokeLater(new Runnable() {
    			@Override
    			public void run() {
    				// FIXME: a better solution is required
    				highlightAll();
    				notifyModified();
    			}
    		});
    	}
    }

    
    /**
     * Reverts one executed command
     */
	private class RevertOneAction extends AbstractAction {
        public void actionPerformed(ActionEvent ev) {
        	int newPos = interpreter.revertOneCommand();
        	if (newPos > writePosition) {
        		// Should never happen
        		System.err.println("revertOne: newPos > writePosition");
        		return;
        	}
        	
        	changeWritePosition(newPos);
        }
	}

	
    /**
     * Reverts several executed commands
     */
	private class RevertAction extends AbstractAction {
        public void actionPerformed(ActionEvent ev) {
        	int pos = getCaretPosition();
        	int newPos = interpreter.revert(pos);
        	if (newPos > writePosition) {
        		// Don't need to change anything
        		return;
        	}
        	
        	changeWritePosition(newPos);
        }
	}
	
	
    /**
     * Inserts the period
     */
	private class InsertPeriodAction extends AbstractAction {
        public void actionPerformed(ActionEvent ev) {
        	replaceSelection(".");
        }
	}

	

    /**
     * Action when "." is pressed
     */
	private class PeriodAction extends AbstractAction {
        public void actionPerformed(ActionEvent ev) {
        	try {
        		int pos = getCaretPosition();
        		boolean placeDot = true;
        		if (pos > 0) {
        			String str = getText(pos - 1, 1);
        			if (str.equals("."))
        				placeDot = false;
        		}
        		
        		if (placeDot)
        			replaceSelection(".");
        		
        		pos = getCaretPosition();
        		if (pos <= writePosition) {
        			System.err.println("pos <= writePosition");
        			return;
        		}
        		
        		// Get all text between the first writable position and the current position
        		String text = getText(writePosition, pos - writePosition);
  
        		// Interpret the text
        		int len = interpreter.interpret(text);

        		// Change the locked text
        		if (len > 0)
        			changeWritePosition(writePosition + len);
        	}
        	catch (Exception e) {
        		System.err.println(e.getMessage());
        	}
        }
    }
}
