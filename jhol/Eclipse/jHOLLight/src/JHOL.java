import java.io.IOException;
import java.text.ParseException;


public class JHOL {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		javax.swing.SwingUtilities.invokeLater(
				  new Runnable() {
				    public void run() {
					System.setProperty("apple.laf.useScreenMenuBar", "true");
					
					System.setProperty("com.apple.mrj.application.apple.menu.about.name", "JHOL");
					
					System.setProperty("com.apple.mrj.application.growbox.intrudes", "false");
					
					System.setProperty("com.apple.macos.smallTabs", "true");
					
					try {
						new edu.pitt.math.jhol.Framework();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (ParseException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					
				    }
					
				  }); 	

	}

}
