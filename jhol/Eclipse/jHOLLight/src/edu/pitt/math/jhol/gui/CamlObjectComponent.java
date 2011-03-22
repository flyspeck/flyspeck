package edu.pitt.math.jhol.gui;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
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

import edu.pitt.math.jhol.core.printer.SelectionTree;

/**
 * A component for displaying Caml objects
 */
@SuppressWarnings("serial")
public class CamlObjectComponent extends JPanel {
	// Description of an element
	public static class Element {
		private SelectionTree tree;
		private int level;
		public int start0, end0;
		public int start1, end1;
		
		public Element(SelectionTree tree) {
			this.tree = tree;
		}
		
		public int getLevel() {
			return level;
		}
		
		public void setLevel(int level) {
			if (level < 0)
				level = 0;
			this.level = level;
		}
		
		public void incLevel() {
			level++;
		}
		
		public void decLevel() {
			level--;
			if (level < 0)
				level = 0;
		}
		
		public void resetSelection() {
			level = 0;
			end0 = start0 = 0;
			end1 = start1 = 0;
		}
		
		public void setSelection0(int symbolIndex) {
			if (tree == null)
				return;
			
			SelectionTree.Subelement e = tree.getSubelement(symbolIndex, level);
			start0 = e.start;
			end0 = e.end;
			setLevel(e.level);
		}

		public void setSelection1(int level, int symbolIndex) {
			if (tree == null)
				return;
			
			SelectionTree.Subelement e = tree.getSubelement(symbolIndex, level);
			start1 = e.start;
			end1 = e.end;
		}
	}
	
	// Default font rendering context
	private static final FontRenderContext frc = new FontRenderContext(null,
			true, false);

	// Element
	private Element element;
	
	// Text for rendering
	private AttributedString text;
	
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
		map.put(TextAttribute.SIZE, new Float(20.0));
	}

	/**
	 * Default constructor
	 */
	public CamlObjectComponent() {
		TestMouseListener m = new TestMouseListener();
		addMouseMotionListener(m);
		addMouseListener(m);
		element = null;
	}
	
	
	/**
	 * Resets the selection region
	 */
	public void resetSelection() {
		if (element != null)
			element.resetSelection();
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
		
		element.setLevel(level);
		element.setSelection0(symbol);
	}

	/**
	 * Initializes the component with a new Caml object
	 */
	public void init(SelectionTree tree) {
		element = new Element(tree);
		text = new AttributedString(tree.toString(), map);

		AttributedCharacterIterator it = text.getIterator();
		start = it.getBeginIndex();
		end = it.getEndIndex();
		lineMeasurer = new LineBreakMeasurer(it, frc);
	}

	/**
	 * Computes the text layout
	 */
	public float computeRows(float width) {
		rows.clear();

		float y = 0;

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

		return y;
	}

	/**
	 * Draws a multiline text
	 */
	public void paint(Graphics g) {
		super.paint(g);
		
		if (element == null)
			return;

		Graphics2D g2 = (Graphics2D) g;

		for (TextRow row : rows) {
			TextLayout layout = row.layout;

			if (element.end1 > element.start1) {
				int first = element.start1, last = element.end1;

				if (first <= row.lastIndex && row.firstIndex <= last) {
					first -= row.firstIndex;
					if (first < 0)
						first = 0;

					last -= row.firstIndex;
					if (last > row.lastIndex - row.firstIndex + 1)
						last = row.lastIndex - row.firstIndex + 1;

					Shape highlight = layout.getLogicalHighlightShape(first,
							last);
					g2.setColor(new Color(184, 255, 183));
					g2.translate(0, row.y);
					g2.fill(highlight);
					g2.translate(0, -row.y);
				}
			}
			
			if (element.end0 > element.start0) {
				int first = element.start0, last = element.end0;

				if (first <= row.lastIndex && row.firstIndex <= last) {
					first -= row.firstIndex;
					if (first < 0)
						first = 0;

					last -= row.firstIndex;
					if (last > row.lastIndex - row.firstIndex + 1)
						last = row.lastIndex - row.firstIndex + 1;

					Shape highlight = layout.getLogicalHighlightShape(first,
							last);
					g2.setColor(Color.red);
					g2.translate(0, row.y);
					g2.draw(highlight);
					g2.translate(0, -row.y);
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

			if (i >= element.start0 && i <= element.end0) {
				element.incLevel();
			} else {
				element.decLevel();
			}
			
			element.setSelection0(i);

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

			if (i >= element.start0 && i <= element.end0) {
				element.setSelection1(element.getLevel() + 1, i);
			} else {
				element.setSelection1(element.getLevel() - 1, i);
			}

			repaint();
		}

		@Override
		public void mouseExited(MouseEvent e) {
			element.start1 = element.end1 = 0;
			repaint();
		}
	}
}
