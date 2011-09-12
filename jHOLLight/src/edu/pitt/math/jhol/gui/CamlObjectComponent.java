package edu.pitt.math.jhol.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.font.FontRenderContext;
import java.awt.font.LineBreakMeasurer;
import java.awt.font.TextAttribute;
import java.awt.font.TextHitInfo;
import java.awt.font.TextLayout;
import java.text.AttributedCharacterIterator;
import java.text.AttributedString;
import java.util.ArrayList;
import java.util.Hashtable;

import javax.swing.JPanel;

import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.core.printer.Printer;
import edu.pitt.math.jhol.core.printer.SelectionTree;

/**
 * A component for displaying Caml objects
 */
@SuppressWarnings("serial")
public class CamlObjectComponent extends JPanel {
	// Description of an element
	public static class Element {
		CamlObject object;
		int level;
		int index;
		
		public Element(CamlObject obj) {
			if (obj == null)
				throw new RuntimeException("obj == null");
			
			this.object = obj;
		}
		
		public void resetSelection() {
			level = 0;
			index = 0;
		}
		
		public void setSelection(int level, int index) {
			this.level = level;
			this.index = index;
		}
		
		@Override
		public int hashCode() {
			return object.hashCode();
		}
		
		@Override
		public boolean equals(Object obj) {
			return object.equals(obj);
		}
		
		@Override
		public String toString() {
			return object.toString();
		}
	}
		
	// Default font rendering context
	private static final FontRenderContext frc = new FontRenderContext(null,
			true, false);

	// If true then a multiline mode is on
	private boolean wordWrap;
	
	// If true then the text layout is changed automatically
	private boolean autoResize;
	
	// Indicates whether the selection should be drawn
	private boolean drawSelection;
	
	// The width of the text
	// If 0 then the width of the component is used
	private int textWidth;
	
	// Element
	private Element element;
	
	// Text for rendering
	private AttributedCharacterIterator text;
	
	// Selection tree
	private SelectionTree tree;
	
	// Selection indices
	private int start0, end0;
	private int start1, end1;
	
	// Tables with attributes
	private static final Hashtable<TextAttribute, Object> map;
	
	// Line breaker
	private LineBreakMeasurer lineMeasurer;
	private int start, end;


	// Describes all rows
	private static class TextRow {
		// Text layout for the row
		public TextLayout layout;

		// Position of the row (first and last y-coordinates)
		public float y0, y1;
		// Base line position
		public float y;

		// First and last indices of symbols on this row
		public int firstIndex, lastIndex;
	}

	// All rows
	private ArrayList<TextRow> rows = new ArrayList<TextRow>();

	/**
	 * Static initializer
	 */
	static {
		map = new Hashtable<TextAttribute, Object>();
		map.put(TextAttribute.FAMILY, Font.MONOSPACED);
		map.put(TextAttribute.SIZE, new Float(14.0));
	}
	
	
	/**
	 * Default constructor
	 */
	public CamlObjectComponent(boolean wordWrapFlag, boolean autoResizeFlag, boolean drawSelection) {
		this.wordWrap = wordWrapFlag;
		this.autoResize = autoResizeFlag;
		this.drawSelection = drawSelection;
		
		// Add a mouse listener
		TestMouseListener m = new TestMouseListener();
		addMouseMotionListener(m);
		addMouseListener(m);
		
		// Add a component listener
		addComponentListener(new ComponentListener() {
			@Override
			public void componentShown(ComponentEvent e) {
			}
			
			@Override
			public void componentResized(ComponentEvent e) {
				if (autoResize) {
					textWidth = 0;
					computeRows();
				}
			}
			
			@Override
			public void componentMoved(ComponentEvent e) {
			}
			
			@Override
			public void componentHidden(ComponentEvent e) {
			}
		});
		
		element = null;
	}
	
	
	/**
	 * Sets the word wrap flag.
	 * The component is not automatically updated. 
	 * @param wordWrap
	 */
	public void setWordWrap(boolean wordWrap) {
		if (this.wordWrap == wordWrap)
			return;
		
		this.wordWrap = wordWrap;
		computeRows();
	}
	
	
	/**
	 * Sets the text width.
	 * The component is not automatically updated.
	 * @param width
	 */
	public void setTextWidth(int width) {
		if (this.textWidth == width)
			return;
		
		this.textWidth = width;
		computeRows();
	}
	
	
	/**
	 * Resets the selection
	 */
	public void resetSelection() {
		if (element != null)
			element.resetSelection();
		end0 = start0 = 0;
		end1 = start1 = 0;
	}
	
	/**
	 * Sets the main selection region
	 * @param symbolIndex
	 */
	protected void setSelection0(int level, int symbolIndex) {
		if (element == null)
			return;
		
		SelectionTree.Subelement e = tree.getSubelement(symbolIndex, level);
		start0 = e.start;
		end0 = e.end;
		element.level = e.level;
		element.index = start0;
	}

	/**
	 * Sets the secondary selection region
	 */
	protected void setSelection1(int level, int symbolIndex) {
		if (element == null)
			return;
		
		SelectionTree.Subelement e = tree.getSubelement(symbolIndex, level);
		start1 = e.start;
		end1 = e.end;
	}
	
	
	/**
	 * Increases the selection level
	 */
	protected void incLevel() {
		if (element == null)
			return;
		
		element.level++;
	}
	
	
	/**
	 * Decreases the selection level
	 */
	protected void decLevel() {
		if (element == null)
			return;
		
		element.level--;
		if (element.level < 0)
			element.level = 0;
	}

	
	/**
	 * Returns the element
	 */
	public Element getElement() {
		return element;
	}
	
	
	/**
	 * Sets the selection
	 */
	public void setSelection(int level, int symbol) {
		if (element == null)
			return;
		
		setSelection0(level, symbol);
	}

	
	/**
	 * Initializes the component with a new Caml object.
	 * Returns the desired height of the component.
	 */
	public float init(CamlObject obj) {
		element = new Element(obj);
		tree = Printer.print(obj);
		AttributedString str = new AttributedString(tree.toString(), map);

		text = str.getIterator();
		start = text.getBeginIndex();
		end = text.getEndIndex();
		lineMeasurer = new LineBreakMeasurer(text, frc);
		
		return computeRows();
	}

	
	/**
	 * Computes the text layout
	 */
	protected float computeRows() {
		rows.clear();
		if (element == null)
			return 0;

		float y = 0;
		int width = (textWidth <= 0) ? getWidth() : textWidth;
		
		if (wordWrap) {
			lineMeasurer.setPosition(start);

			while (lineMeasurer.getPosition() < end) {
				// Compute attributes of the next row
				int firstIndex = lineMeasurer.getPosition();
				TextLayout layout = lineMeasurer.nextLayout(width);
				int lastIndex = lineMeasurer.getPosition() - 1;

				float y0 = y;
				float yy = y0 + layout.getAscent();
				float y1 = yy + layout.getDescent();

				TextRow row = new TextRow();
				row.layout = layout;
				row.firstIndex = firstIndex;
				row.lastIndex = lastIndex;
				row.y = yy;
				row.y0 = y0;
				row.y1 = y1;

				rows.add(row);

				y = y1 + layout.getLeading();
			}
		}
		else {
			// Create one layout
			TextRow row = new TextRow();
			row.layout = new TextLayout(text, frc);
			row.firstIndex = start;
			row.lastIndex = end;
			row.y = row.layout.getAscent();
			row.y0 = 0;
			row.y1 = row.y + row.layout.getDescent();
			
			rows.add(row);
			
			y = row.y1 + row.layout.getLeading();
		}
		
		setPreferredSize(new Dimension((int)width, (int) y));

		return y;
	}

	
	/**
	 * Draws the text
	 */
	@Override
	public void paint(Graphics g) {
		super.paint(g);
		
		if (element == null)
			return;

		Graphics2D g2 = (Graphics2D) g;

		for (TextRow row : rows) {
			TextLayout layout = row.layout;

			if (drawSelection) {
				// Draw the secondary selection
				if (end1 > start1) {
					int first = start1, last = end1;

					if (first <= row.lastIndex && row.firstIndex <= last) {
						first -= row.firstIndex;
						if (first < 0)
							first = 0;

						last -= row.firstIndex;
						if (last > row.lastIndex - row.firstIndex + 1)
							last = row.lastIndex - row.firstIndex + 1;

						Shape highlight = layout.getLogicalHighlightShape(
								first, last);
						g2.setColor(new Color(184, 255, 183));
						g2.translate(0, row.y);
						g2.fill(highlight);
						g2.translate(0, -row.y);
					}
				}

				// Draw the main selection
				if (end0 > start0) {
					int first = start0, last = end0;

					if (first <= row.lastIndex && row.firstIndex <= last) {
						first -= row.firstIndex;
						if (first < 0)
							first = 0;

						last -= row.firstIndex;
						if (last > row.lastIndex - row.firstIndex + 1)
							last = row.lastIndex - row.firstIndex + 1;

						Shape highlight = layout.getLogicalHighlightShape(
								first, last);
						g2.setColor(Color.red);
						g2.translate(0, row.y);
						g2.draw(highlight);
						g2.translate(0, -row.y);
					}
				}
			}

			g2.setColor(Color.BLACK);
			row.layout.draw(g2, 0, row.y);
		}
	}
	
	
	/**
	 * Returns a row for which y0 <= y <= y1
	 */
	private TextRow findRow(float y) {
		for (TextRow row : rows) {
			if (row.y0 <= y && y <= row.y1)
				return row;
		}

		return null;
	}

	/**
	 * Mouse listener
	 */
	private class TestMouseListener extends MouseAdapter {
		/**
		 * Compute the character position of the mouse click.
		 */
		public void mouseClicked(MouseEvent e) {
			if (element == null)
				return;

			float x = (float) e.getX();
			float y = (float) e.getY();

			TextRow row = findRow(y);
			if (row == null)
				return;

			// Get the character position of the mouse click. TextHitInfo
			TextHitInfo currentHit = row.layout.hitTestChar(x, y);
			int i = currentHit.getCharIndex() + row.firstIndex;

			if (i >= start0 && i <= end0) {
				incLevel();
			} else {
				decLevel();
			}
			
			setSelection0(element.level, i);

			mouseMoved(e);
			repaint();
		}

		@Override
		public void mouseMoved(MouseEvent e) {
			if (element == null)
				return;
			
			float x = (float) e.getX();
			float y = (float) e.getY();

			TextRow row = findRow(y);
			if (row == null)
				return;

			// Get the character position of the mouse click.
			TextHitInfo currentHit = row.layout.hitTestChar(x, y);
			int i = currentHit.getCharIndex() + row.firstIndex;

			if (i >= start0 && i <= end0) {
				setSelection1(element.level + 1, i);
			} else {
				setSelection1(element.level - 1, i);
			}

			repaint();
		}

		@Override
		public void mouseExited(MouseEvent e) {
			start1 = end1 = 0;
			repaint();
		}
	}
}
