package edu.pitt.math.jhol;

import java.io.IOException;
import java.io.InputStream;

import javax.swing.JTextPane;



 class HOLStream extends java.io.PushbackInputStream {


@SuppressWarnings("unused")
private JTextPane textPane;	
	
	protected HOLStream(InputStream arg0, JTextPane textPane) {
		super(arg0);
		
		this.textPane = textPane;
	}

	
	
	public int read (byte[] b,int off,int len) throws IOException{
		if (off != 0 || len != b.length)
			return super.read(b,off,len);
		int result = super.read(b, off, len);
		if (result == -1)
			return result;
		
		if (b[0] == '<'){
			
				for (;result < 5;b[result++] = (byte) super.read());
			if(  hasHTML(b,1)  ){
				/*unread(b,0,result);
				this.in.
				while (html.indexOf("<HTML>") != -1) {
					int start = html.indexOf("<HTML>");
					// console.print(html.substring(0, start));//Print any text that
					// occurs before the HTML
					int end = html.indexOf("</HTML>");
					String htmlText = html.substring(start, end + 7);
					JLabel tmpLabel = htmlToJLabel(htmlText);

					((JTextPane) consoleTextPane).insertComponent(tmpLabel);
					html = html.substring(end + 7, html.length());
				}
				print(html);
				return 0;
			*/}
		}
		
		for (int i = 1; i < result; i++){
			if (b[i] == '<'){
				this.unread(b, i, result - i);
				return i;
			}
				
		}
			return result;
	}
	
	private  boolean hasHTML(byte[] b, int off) {
		off--;
		return (b[off + 1] == 'H' || b[off + 1] == 'h')
		&& (b[off + 2] == 'T' || b[off + 2] == 't')
		&& (b[off + 3] == 'M' || b[off + 3] == 'm')
		&& (b[off + 4] == 'L' || b[off + 4] == 'l');
	}
	
}
