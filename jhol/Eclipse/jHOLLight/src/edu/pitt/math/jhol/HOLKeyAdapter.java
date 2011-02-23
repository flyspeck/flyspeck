package edu.pitt.math.jhol;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.LinkedList;
import java.util.List;

public class HOLKeyAdapter extends KeyAdapter{
	private HOLLightWrapper hol; 
	HOLKeyAdapter(HOLLightWrapper hol){
        this.hol = hol;
	}
        //handle other methods
        public void keyPressed(KeyEvent e){
        	
        if (e.isControlDown() && e.getKeyCode() == KeyEvent.VK_C){
        	hol.interrupt();
        }
        
        else if  (e.getKeyCode() != KeyEvent.VK_ENTER )
                return;
        
            //Main Loop
            List<String> cmdList = new LinkedList<String>();
            //          do
            //{
                //in case someone pastes more than one command into the buffer          
                String line = hol.getLine();
                cmdList.add(line);
                //          }while(bufInput.ready());
            while(cmdList.size() != 0){
            hol.runCommand(((LinkedList<String>) cmdList).removeFirst()  + "\n");
            }          
            //updateTopGoal();
        }
    }

