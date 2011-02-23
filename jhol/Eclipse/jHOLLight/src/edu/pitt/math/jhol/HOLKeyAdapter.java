package edu.pitt.math.jhol;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.LinkedList;
import java.util.List;

import javax.swing.SwingUtilities;

public class HOLKeyAdapter extends KeyAdapter{
	private HOLLightWrapper hol; 
	HOLKeyAdapter(HOLLightWrapper hol){
        this.hol = hol;
	}
        //handle other methods
        public void keyPressed(KeyEvent e){
        	if (!SwingUtilities.isEventDispatchThread())
        		throw new RuntimeException("EDT@");
        if (e.isControlDown() && e.getKeyCode() == KeyEvent.VK_C){
        	hol.interrupt();
        }
        
        else if  (e.getKeyCode() != KeyEvent.VK_ENTER )
                return;
        
            
            //updateTopGoal();
        }
    }

