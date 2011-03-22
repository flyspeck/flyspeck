package edu.pitt.math.jhol.test;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.font.FontRenderContext;
import java.awt.font.TextHitInfo;
import java.awt.font.TextLayout;
import java.awt.geom.Point2D;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.BoxLayout;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;

import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.parser.Parser;
import edu.pitt.math.jhol.core.printer.Printer;
import edu.pitt.math.jhol.core.printer.TermPrinter;
import edu.pitt.math.jhol.core.printer.TermPrinterData;
import edu.pitt.math.jhol.core.printer.SelectionTree;

@SuppressWarnings("serial")
public class SubtermSelectionTest extends JComponent {
	// The TextLayout to draw and hit-test.
	private TextLayout textLayout;
	private SelectionTree term;

	JLabel selectedTerm;

	private int start0, end0;
	private int start1, end1;
	private int level;

	public SubtermSelectionTest(Term tm) {

		FontRenderContext frc = new FontRenderContext(null, true, false);

		this.term = TermPrinter.print(tm);
		Font font = new Font(Font.SANS_SERIF, Font.BOLD, 20);

		// Create a new TextLayout from the given text.
		textLayout = new TextLayout(term.toString(), font, frc);

		start0 = end0 = 0;
		start1 = end1 = 0;
		level = 0;
		
		SelectionTree.Subelement stm = term.getSubelement(0, 0);
		start0 = stm.start;
		end0 = stm.end;
		
		selectedTerm = new JLabel();
		selectedTerm.setText(Printer.print(stm.element).toString());
		

		addMouseListener(new HitTestMouseListener());
		addMouseMotionListener(new HitTestMouseListener());
	}

	/**
	 * Compute a location within this Component for textLayout's origin, such
	 * that textLayout is centered horizontally and vertically.
	 * 
	 * Note that this location is unknown to textLayout; it is used only by this
	 * Component for positioning.
	 */
	private Point2D computeLayoutOrigin() {

		Dimension size = getSize();

		Point2D.Float origin = new Point2D.Float();

		origin.x = (float) (size.width - textLayout.getAdvance()) / 2;
		origin.y = (float) (size.height - textLayout.getDescent() + textLayout
				.getAscent()) / 2;

		return origin;
	}

	/**
	 * Draw textLayout and the carets corresponding to the most recent mouse
	 * click (if any).
	 */
	public void paint(Graphics g) {

		Graphics2D graphics2D = (Graphics2D) g;

		Point2D origin = computeLayoutOrigin();

		// Since the caret Shapes are relative to the origin
		// of textLayout, we'll translate the graphics so that
		// the origin of the graphics is where we want textLayout
		// to appear.

		graphics2D.translate(origin.getX(), origin.getY());

		boolean haveCaret = start1 == end1;

		if (!haveCaret) {
			Shape highlight = textLayout.getLogicalHighlightShape(start1, end1);
			graphics2D.setColor(new Color(184, 255, 183));
			graphics2D.fill(highlight);
		}

		
		haveCaret = start0 == end0;

		if (!haveCaret) {
			Shape highlight = textLayout.getLogicalHighlightShape(start0, end0);
			graphics2D.setColor(Color.red);
			graphics2D.draw(highlight);
		}


		
		graphics2D.setColor(Color.black);

		// Draw textLayout.
		textLayout.draw(graphics2D, 0, 0);

/*		// Retrieve caret Shapes for insertionIndex.
		Shape[] carets = textLayout.getCaretShapes(insertionIndex);

		// Draw the carets. carets[0] is the strong caret, and
		// is never null. carets[1], if it is not null, is the
		// weak caret.
		graphics2D.setColor(STRONG_CARET_COLOR);
		graphics2D.draw(carets[0]);

		if (carets[1] != null) {
			graphics2D.setColor(WEAK_CARET_COLOR);
			graphics2D.draw(carets[1]);
		}*/
	}

	private class HitTestMouseListener extends MouseAdapter {

		/**
		 * Compute the character position of the mouse click.
		 */
		public void mouseClicked(MouseEvent e) {

			Point2D origin = computeLayoutOrigin();

			// Compute the mouse click location relative to
			// textLayout's origin.
			float clickX = (float) (e.getX() - origin.getX());
			float clickY = (float) (e.getY() - origin.getY());

			// Get the character position of the mouse click.
			TextHitInfo currentHit = textLayout.hitTestChar(clickX, clickY);
			int i = currentHit.getCharIndex();
			
			SelectionTree.Subelement stm;
			if (i >= start0 && i <= end0) {
				level++;
			}
			else {
				level--;
			}
			
			stm = term.getSubelement(i, level);
			start0 = stm.start;
			end0 = stm.end;
			level = stm.level;
			
			selectedTerm.setText(level + ": " + Printer.print(stm.element).toString());
			mouseMoved(e);
			
			repaint();
		}

		@Override
		public void mouseMoved(MouseEvent e) {
			Point2D origin = computeLayoutOrigin();

			// Compute the mouse click location relative to
			// textLayout's origin.
			float clickX = (float) (e.getX() - origin.getX());
			float clickY = (float) (e.getY() - origin.getY());

			// Get the character position of the mouse click.
			TextHitInfo currentHit = textLayout.hitTestChar(clickX, clickY);
			int i = currentHit.getCharIndex();

			SelectionTree.Subelement stm;
			if (i >= start0 && i <= end0) {
				stm = term.getSubelement(i, level + 1);
			}
			else {
				stm = term.getSubelement(i, level - 1);
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

	public static void main(String[] args) throws Exception {
		TermPrinterData.init();
        String str1 = "Comb(Comb(Comb(Const(\"COND\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyvar(\"?959859\"),Tyapp(\"fun\"[Tyvar(\"?959859\"),Tyvar(\"?959859\")])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Var(\"f\",Tyapp(\"fun\"[Tyvar(\"?959867\"),Tyvar(\"?959859\")])),Var(\"x\",Tyvar(\"?959867\")))),Comb(Var(\"g\",Tyapp(\"fun\"[Tyvar(\"?959868\"),Tyvar(\"?959859\")])),Var(\"y\",Tyvar(\"?959868\"))))";
        String str2 = "Comb(Comb(Const(\"real_add\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])),Comb(Comb(Const(\"DECIMAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))),Comb(Comb(Const(\"DECIMAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))))))))))))))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT0\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))))))";
        String str3 = "Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"a\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"b\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])))))";
        String str4 = "Comb(Comb(Const(\"INSERT\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"s\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])])))";
        String str5 = "Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%2368\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%2368\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"x\",Tyapp(\"num\"[]))))),Var(\"x\",Tyapp(\"num\"[])))))))";
        String str6 = "Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%2378\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"num\"[])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"num\"[])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%2378\",Tyapp(\"num\"[]))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[])))))),Comb(Var(\"P\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])),Var(\"x\",Tyapp(\"num\"[]))))),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Var(\"x\",Tyapp(\"num\"[]))),Var(\"y\",Tyapp(\"num\"[]))))))))))";
        String str = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"hull\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Const(\"convex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]))),Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Const(\"GSPEC\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])),Abs(Var(\"GEN%PVAR%698\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Comb(Const(\"SETSPEC\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])])),Var(\"GEN%PVAR%698\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"FINITE\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"SUBSET\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"p\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"<=\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"CARD\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"num\"[])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])),Comb(Const(\"dimindex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"N\"),Tyapp(\"bool\"[])]),Tyapp(\"num\"[])])),Const(\"UNIV\",Tyapp(\"fun\"[Tyvar(\"N\"),Tyapp(\"bool\"[])])))),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Const(\"==>\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"IN\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])))),Comb(Comb(Const(\"real_le\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))),Comb(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Var(\"x\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))))))),Comb(Comb(Const(\"/\\\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"sum\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])]),Tyapp(\"real\"[])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])))),Comb(Const(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])),Comb(Const(\"NUMERAL\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Comb(Const(\"BIT1\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])),Const(\"_0\",Tyapp(\"num\"[]))))))),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"vsum\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Var(\"s\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"bool\"[])]))),Abs(Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])),Comb(Comb(Const(\"%\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])),Comb(Var(\"u\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])),Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))),Var(\"v\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])))))),Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))))))))))))),Var(\"y\",Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]))))))))))";
		
		String[] strs = new String[] {str1, str2, str3, str4, str5, str6, str};
		Term[] tms = new Term[strs.length];
		for (int i = 0; i < strs.length; i++) {
			tms[i] = Parser.parseTerm(strs[i]);
		}
		

		JFrame sampleFrame = new JFrame("Demo");

		
		sampleFrame.setLayout(new BoxLayout(sampleFrame.getContentPane(),
				BoxLayout.PAGE_AXIS));
		
		for (int i = 0; i < tms.length; i++) {
			SubtermSelectionTest sample = new SubtermSelectionTest(tms[i]);
			sampleFrame.add(sample);
			sampleFrame.add(sample.selectedTerm);
		}

		sampleFrame.setBackground(Color.white);
		sampleFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		sampleFrame.setSize(1600, tms.length * 60);
		sampleFrame.setVisible(true);
	}
}