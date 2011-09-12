package edu.pitt.math.jhol.test;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
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

import javax.swing.AbstractCellEditor;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JColorChooser;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.parser.Parser;
import edu.pitt.math.jhol.core.printer.Printer;
import edu.pitt.math.jhol.core.printer.TermPrinterData;
import edu.pitt.math.jhol.core.printer.SelectionTree;
import edu.pitt.math.jhol.gui.CamlObjectComponent;
import edu.pitt.math.jhol.gui.CamlObjectTable;

@SuppressWarnings("serial")
public class MultilineTermTest extends JPanel {
	// Statistic variables
	static int paintCounter;
	static int renderCounter;
	static int editCounter;
	
	static JLabel paintLabel;
	static JLabel renderLabel;
	static JLabel editLabel;
	
	
	
	private static final FontRenderContext frc = new FontRenderContext(null,
			true, false);

	private SelectionTree tree;
	private AttributedString text;
	private static final Hashtable<TextAttribute, Object> map;
	private LineBreakMeasurer lineMeasurer;
	private int start, end;

	private int level = 0;
	private int start0 = 0, end0 = 0;
	private int start1 = 0, end1 = 0;

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
	public MultilineTermTest() {
		TestMouseListener m = new TestMouseListener();
		addMouseMotionListener(m);
		addMouseListener(m);
	}
	
	
	/**
	 * Resets the selection region
	 */
	public void resetSelection() {
		level = 0;
		start0 = end0 = 0;
		start1 = end1 = 0;
	}
	
	
	public int getLevel() {
		return level;
	}
	
	
	public int getStart() {
		return start0;
	}
	
	
	public int getEnd() {
		return end0;
	}
	
	
	public TableModel.Element getElement() {
		return new TableModel.Element(tree, level, start0);
	}
	
	
	/**
	 * Sets a selection
	 */
	public void setSelection(int level, int symbol) {
		this.level = level;
		SelectionTree.Subelement subterm = tree.getSubelement(symbol, level);
		start0 = subterm.start;
		end0 = subterm.end;
	}

	/**
	 * Default constructor
	 * 
	 * @param text
	 */
	public void init(SelectionTree tree) {
		this.tree = tree;
		this.text = new AttributedString(tree.toString(), map);

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

		setPreferredSize(new Dimension((int)width, (int) y));
		
		return y;
	}

	/**
	 * Draws a multiline text
	 */
	public void paint(Graphics g) {
		paintCounter++;
		paintLabel.setText(String.valueOf(paintCounter));
		super.paint(g);

		Graphics2D g2 = (Graphics2D) g;

		for (TextRow row : rows) {
			TextLayout layout = row.layout;

			if (end1 > start1) {
				int first = start1, last = end1;

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
			
			if (end0 > start0) {
				int first = start0, last = end0;

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

			float x = (float) e.getX();
			float y = (float) e.getY();

			TextRow row = findRow(y);
			if (row == null)
				return;

			// Get the character position of the mouse click. TextHitInfo
			TextHitInfo currentHit = row.layout.hitTestChar(x, y);
			int i = currentHit.getCharIndex() + row.firstIndex;

			SelectionTree.Subelement stm;
			if (i >= start0 && i <= end0) {
				level++;
			} else {
				level--;
			}

			stm = tree.getSubelement(i, level);
			start0 = stm.start;
			end0 = stm.end;
			level = stm.level;

			mouseMoved(e);
			repaint();
		}

		@Override
		public void mouseMoved(MouseEvent e) {
			float x = (float) e.getX();
			float y = (float) e.getY();

			TextRow row = findRow(y);
			if (row == null)
				return;

			// Get the character position of the mouse click.
			TextHitInfo currentHit = row.layout.hitTestChar(x, y);
			int i = currentHit.getCharIndex() + row.firstIndex;

			SelectionTree.Subelement stm;
			if (i >= start0 && i <= end0) {
				stm = tree.getSubelement(i, level + 1);
			} else {
				stm = tree.getSubelement(i, level - 1);
			}

			start1 = stm.start;
			end1 = stm.end;

			repaint();
		}

		@Override
		public void mouseExited(MouseEvent e) {
			start1 = end1 = 0;
			repaint();
		}
	}

	/**
	 * Main
	 * 
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
		TermPrinterData.init();

		// Create several terms
		String str1 = "Comb(Comb(Comb(Const(\"COND\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyvar(\"?959859\"),Tyapp(\"fun\"[Tyvar(\"?959859\"),Tyvar(\"?959859\")])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Var(\"f\",Tyapp(\"fun\"[Tyvar(\"?959867\"),Tyvar(\"?959859\")])),Var(\"x\",Tyvar(\"?959867\")))),Comb(Var(\"g\",Tyapp(\"fun\"[Tyvar(\"?959868\"),Tyvar(\"?959859\")])),Var(\"y\",Tyvar(\"?959868\"))))";
		String str2 = "Comb(Comb(Const(\"real_add\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Comb(Const(\"DECIMAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))),Comb(Comb(Const(\"DECIMAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))))))";
		String str3 = "Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"a\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"b\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])))))";
		String str4 = "Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"s\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])])))";
		String str5 = "Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%2368\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%2368\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"x\",Tyapp(\"num\"[]))))),Var(\"x\",Tyapp(\"num\"[])))))))";
		String str6 = "Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%2378\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"num\"[])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%2378\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"x\",Tyapp(\"num\"[]))))),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Var(\"y\",Tyapp(\"num\"[]))))))))))";
		String str = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"hull\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Const(\"convex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]))),Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%698\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%698\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"FINITE\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"SUBSET\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"<=\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"CARD\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"num\"[])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Comb(Const(\"dimindex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"N\"),Tyapp(\"bool\"[])]),Tyapp(\"num\"[])])),Const(\"UNIV\",Tyapp(\"fun\"[Tyvar(\"N\"),Tyapp(\"bool\"[])])))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Const(\"==>\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"real_le\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))))))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"sum\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])]),Tyapp(\"real\"[])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])))),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"vsum\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Abs(Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))),Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))))),Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))))))))))))),Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))))))))))";

		String[] strs = new String[] { str1, str2, str3, str4, str5, str6, str };
		int n = 100;
		Term[] tms = new Term[strs.length * n];
		
		Term t0 = Parser.parseTerm(str);
		Term t1 = Parser.parseTerm(str2);
		
		for (int i = 0; i < tms.length; i++) {
//			tms[i] = Parser.parseTerm(strs[i % strs.length]);
			tms[i] = i > 0 ? t1 : t0;
		}

		// Create a Java frame
		JFrame sampleFrame = new JFrame("Demo");
		sampleFrame.setLayout(new BoxLayout(sampleFrame.getContentPane(),
				BoxLayout.PAGE_AXIS));
		
		CamlObjectComponent cc = new CamlObjectComponent(true, true, true);
		cc.init(t0);
		sampleFrame.add(cc);
		
		paintLabel = new JLabel("0");
		renderLabel = new JLabel("0");
		editLabel = new JLabel("0");
		
		sampleFrame.add(paintLabel);
		sampleFrame.add(renderLabel);
		sampleFrame.add(editLabel);

		edu.pitt.math.jhol.gui.CamlObjectList list = new edu.pitt.math.jhol.gui.CamlObjectList();
		for (int i = 0; i < tms.length; i++)
			list.add(tms[i]);
		
		JTable x = new CamlObjectTable(list);
		JScrollPane xx = new JScrollPane(x);
		
		sampleFrame.add(xx);
		
		// Create a table with a custom cell renderer
		JTable table = new JTable(new TableModel(tms)) {
			private TableCellRenderer renderer = new TableModel.TermRenderer();
			private TableCellEditor editor = new TestEditor();

			@Override
			public TableCellRenderer getCellRenderer(int row, int column) {
				if (column == 0)
					return renderer;
				else
					return super.getCellRenderer(row, column);
			}

			@Override
			public TableCellEditor getCellEditor(int row, int column) {
				if (column == 0)
					return editor;
				else
					return super.getCellEditor(row, column);
			}

		};

		table.getColumnModel().getColumn(1).setCellEditor(new ColorEditor());

		// Put the table into a scroll pane
		JScrollPane scroll = new JScrollPane(table);

		sampleFrame.add(scroll);

		// sampleFrame.add(new
		// MultilineTextTest("If you have a paragraph of styled text that you would like to fit within a specific width, you can use the LineBreakMeasurer class. This class enables styled text to be broken into lines so that they fit within a particular visual advance. Each line is returned as a TextLayout object, which represents unchangeable, styled character data. However, this class also enables access to layout information. The getAscent and getDescent methods of TextLayout return information about the font that is used to position the lines in the component. The text is stored as an AttributedCharacterIterator object so that the font and point size attributes can be stored with the text."));
		sampleFrame.setBackground(Color.white);
		sampleFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		sampleFrame.setSize(300, 500);
		sampleFrame.setVisible(true);
	}
}

/**
 * Cell editor
 */
@SuppressWarnings("serial")
class ColorEditor extends AbstractCellEditor implements TableCellEditor,
		ActionListener {
	Color currentColor;
	JButton button;
	JColorChooser colorChooser;
	JDialog dialog;
	protected static final String EDIT = "edit";

	public ColorEditor() {
		button = new JButton();
		button.setActionCommand(EDIT);
		button.addActionListener(this);
		button.setBorderPainted(false);

		// Set up the dialog that the button brings up.
		colorChooser = new JColorChooser();
		dialog = JColorChooser.createDialog(button, "Pick a Color", true, // modal
				colorChooser, this, // OK button handler
				null); // no CANCEL button handler
	}

	public void actionPerformed(ActionEvent e) {
		if (EDIT.equals(e.getActionCommand())) {
			// The user has clicked the cell, so
			// bring up the dialog.
			button.setBackground(currentColor);
			colorChooser.setColor(currentColor);
			dialog.setVisible(true);

			fireEditingStopped(); // Make the renderer reappear.

		} else { // User pressed dialog's "OK" button.
			currentColor = colorChooser.getColor();
		}
	}

	// Implement the one CellEditor method that AbstractCellEditor doesn't.
	public Object getCellEditorValue() {
		return currentColor;
	}

	// Implement the one method defined by TableCellEditor.
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		currentColor = Color.RED;
		return button;
	}
}

@SuppressWarnings("serial")
class TestEditor extends AbstractCellEditor implements TableCellEditor {
	protected static final String EDIT = "edit";
	private MultilineTermTest test = new MultilineTermTest();

	public TestEditor() {
	}

	public void actionPerformed(ActionEvent e) {
		if (EDIT.equals(e.getActionCommand())) {
//			test.resetSelection();
			// The user has clicked the cell, so
			// bring up the dialog.

//			fireEditingStopped(); // Make the renderer reappear.

		} else { // User pressed dialog's "OK" button.
		}
	}

	// Implement the one CellEditor method that AbstractCellEditor doesn't.
	public Object getCellEditorValue() {
		return test.getElement();
	}

	// Implement the one method defined by TableCellEditor.
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		if (!(value instanceof TableModel.Element))
			return null;

		TableModel.Element element = (TableModel.Element) value;
		
		MultilineTermTest.editCounter++;
		MultilineTermTest.editLabel.setText(String.valueOf(MultilineTermTest.editCounter));
		
		test.init(element.tree);
		test.setSelection(element.level, element.symbol);
		test.computeRows(table.getColumnModel().getColumn(column).getWidth());
		return test;
	}
}

/**
 * A table model
 * 
 * @author Alexey
 * 
 */
@SuppressWarnings("serial")
class TableModel extends AbstractTableModel {
	/**
	 * Renderer for terms
	 * 
	 * @author Alexey
	 * 
	 */
	static class TermRenderer extends MultilineTermTest implements
			TableCellRenderer {
		public TermRenderer() {
			setOpaque(true);
		}

		@Override
		public Component getTableCellRendererComponent(JTable table,
				Object value, boolean isSelected, boolean hasFocus, int row,
				int column) {

			if (!(value instanceof Element))
				return null;

			MultilineTermTest.renderCounter++;
			MultilineTermTest.renderLabel.setText(String.valueOf(MultilineTermTest.renderCounter));

			Element element = (Element) value;
			
			init(element.tree);
			setSelection(element.level, element.symbol);

			if (isSelected) {
				setBackground(Color.LIGHT_GRAY);
			} else {
				setBackground(Color.WHITE);
			}

			int w = table.getColumnModel().getColumn(0).getWidth();
			float y = computeRows(w);

			if (table.getRowHeight(row) != (int) y) {
				table.setRowHeight(row, (int) y);
			}

			return this;
		}

	}

	// Describes an element of the table
	static class Element {
		SelectionTree tree;
		int level;
		int symbol;
		
		public Element(Term t) {
			this(Printer.print(t), 0, 0);
		}
		
		public Element(SelectionTree tree, int level, int symbol) {
			this.tree = tree;
			this.level = level;
			this.symbol = symbol;
		}
	}
	
	// All elements
	private Element[] elements;

	/**
	 * Default constructor
	 * 
	 * @param terms
	 */
	public TableModel(Term[] ts) {
		elements = new Element[ts.length];

		for (int i = 0; i < ts.length; i++) {
			elements[i] = new Element(ts[i]);
		}
	}

	@Override
	public int getColumnCount() {
		return 2;
	}

	@Override
	public int getRowCount() {
		return elements.length;
	}

	@Override
	public boolean isCellEditable(int row, int column) {
		return true;
	}

	@Override
	public Object getValueAt(int rowIndex, int columnIndex) {
		if (columnIndex == 0)
			return elements[rowIndex];
		else
			return 100;
	}
	

	@Override
    public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
		if (columnIndex == 0) {
			if (aValue instanceof Element && aValue != null)
				elements[rowIndex] = (Element) aValue;
		}
	}


}
