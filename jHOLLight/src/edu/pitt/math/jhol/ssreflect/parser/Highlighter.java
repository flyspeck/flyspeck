package edu.pitt.math.jhol.ssreflect.parser;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Hashtable;

/**
 * Associates different styles with different parts of a text
 */
public class Highlighter {
	/**
	 * Describes a style
	 */
	public static class Style {
		// Bold
		private boolean boldFlag;
		// Italic
		private boolean italicFlag;
		// rgb color 
		private int rgb;
		
		/**
		 * Constructor
		 */
		public Style(boolean bold, boolean italic, int rgb) {
			this.boldFlag = bold;
			this.italicFlag = italic;
			this.rgb = rgb;
		}
		
		public Style(int rgb) {
			this(false, false, rgb);
		}
		
		/**
		 * Bold flag
		 */
		public boolean isBold() {
			return boldFlag;
		}
		
		/**
		 * Italic flag
		 */
		public boolean isItalic() {
			return italicFlag;
		}
		
		/**
		 * Color
		 */
		public int getColor() {
			return rgb;
		}
	}
	
	
	/**
	 * Associates a style to a segment of a text
	 */
	public static class Segment {
		// The position of the first symbol of the segment and
		// the length of the segment.
		public final int start, length;

		// The corresponding style
		public final Style style;
		
		/**
		 * Constructor
		 */
		public Segment(int start, int length, Style style) {
			this.start = start;
			this.length = length;
			this.style = style;
		}
	}
	
	
	/**
	 * Describes a keyword that need to be highlighted
	 */
	static class Keyword {
		// The type of the corresponding token
		private final TokenType tokenType;
		// The value of the corresponding token		
		private final String tokenValue;
		
		/**
		 * Constructor
		 */
		public Keyword(TokenType type, String value) {
			assert(type != null);
			this.tokenType = type;
			this.tokenValue = value;
		}
		
		public Keyword(String value) {
			this(TokenType.IDENTIFIER, value);
		}
		
		@Override
		public int hashCode() {
			int hash = tokenType.hashCode();
			if (tokenValue != null)
				hash += 31 * tokenValue.hashCode();
			
			return hash;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			
			if (!(obj instanceof Keyword))
				return false;
			
			Keyword k2 = (Keyword) obj;
			// Compare types (not null always)
			if (!tokenType.equals(k2.tokenType))
				return false;
			
			// Compare values (could be null)
			if (tokenValue == null)
				return k2.tokenValue == null;
			
			return tokenValue.equals(k2.tokenValue);
		}
		
		@Override
		public String toString() {
			return "Keyword(" + tokenType + ", " + tokenValue + ")";
		}
	}
	
	// The table containing all keywords and associated styles
	private final Hashtable<Keyword, Style> keywords = new Hashtable<Keyword, Style>();

	
	/**
	 * Constructor
	 */
	public Highlighter() {
		// Test styles and keywords
		Style style1 = new Style(true, false, 0x0000A0);
		Style style2 = new Style(true, false, 0x000000);
		Style style3 = new Style(false, false, 0x008000);
		
		String[] keys = new String[] {"rewrite", "move", "case", 
							"elim", "rewr", "have", "set",
							"right", "apply", "split", "left"};

		for (String key : keys) {
			keywords.put(new Keyword(key), style1);
		}
		
		keys = new String[] {"Section", "Variable", "Hypothesis", "Lemma", "Qed", "Abort"};
		for (String key : keys) {
			keywords.put(new Keyword(key), style2);
		}
		
		keywords.put(new Keyword(TokenType.STRING, null), style3);
	}
	
	
	/**
	 * Associates styles with segments of the given text
	 */
	public ArrayList<Segment> highlight(String text) throws Exception {
		assert(text != null);
		
		ArrayList<Segment> result = new ArrayList<Segment>();
		Scanner scanner = new Scanner(new StringReader(text));
		
		int start = 0;
		int end = 0;
		
		while (true) {
			start = end;
			Token t = scanner.nextToken();
			if (t.type == TokenType.EOF)
				break;

			end = t.ch + scanner.yylength();
			
			// We are not interested in values of strings
			Keyword key;
			if (t.type == TokenType.STRING)
				key = new Keyword(t.type, null);
			else
				key = new Keyword(t.type, t.value);
			
			Style style = keywords.get(key);
			if (style == null) {
				continue;
			}
			
			Segment s = new Segment(start, end - start, style);
			result.add(s);
		}
		
		return result;
	}
}
