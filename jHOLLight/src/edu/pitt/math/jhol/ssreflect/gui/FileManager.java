package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import edu.pitt.math.jhol.utils.FileUtils;


/**
 * For working with files
 */
public class FileManager implements Configuration.Saver {
	/* For recently open files */
	private final JMenu fileMenu;
	// Action listener for the file menu
	private final ActionListener fileActionListener;
	
	/* List of all recent files */
	private final ArrayList<FileInfo> recentFiles;
	
	// Currently open file
	private FileInfo currentFile;
	
	// The maximum number of recent files in the menu
	private static final int MAX_RECENT_FILES = 10;
	
	private static final String CONF_RECENT_GROUP = "files.recent";
	private static final String CONF_CURRENT_GROUP = "files.current";
	
	public static final String CMD_FILE_RECENT = "file-recent:";
	
	/**
	 * Describes a recently open file
	 */
	static class FileInfo {
		// File
		public final File file;
		// Position of the caret inside the file
		private int position;
		
		public FileInfo(File file, int position) {
			assert(file != null);
			this.file = file;
			this.position = position;
		}
		
		public FileInfo(String name, int position) {
			this(new File(name), position);
		}
		
		public int getPosition() {
			return position;
		}
		
		@Override
		public int hashCode() {
			return file.hashCode();
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			
			if (!(obj instanceof FileInfo))
				return false;
			
			// Compare files only
			FileInfo info2 = (FileInfo) obj;
			return file.equals(info2.file);
		}
		
		@Override
		public String toString() {
			return file.toString();
		}
	}

	/**
	 * Listens for changes of the current file
	 *
	 */
	public interface CurrentFileListener {
		public void currentFileChanged(File currentFile);
	}
	
	// Array of all listeners
	private final ArrayList<CurrentFileListener> currentFileListeners;
	
	
	
	/**
	 * Creates a config file reader
	 */
	public FileManager(Configuration conf, JMenu fileMenu, ActionListener actionListener) {
		this.fileMenu = fileMenu;
		this.fileActionListener = actionListener;
		this.recentFiles = new ArrayList<FileInfo>();
		this.currentFileListeners = new ArrayList<CurrentFileListener>();
		this.currentFile = null;
		readConfiguration(conf);
	}
	
	
	/**
	 * Adds a listener
	 */
	public void addCurrentFileListener(CurrentFileListener listener) {
		if (listener != null)
			currentFileListeners.add(listener);
	}
	
	
	/**
	 * Returns the currently open file
	 */
	public FileInfo getCurrentFile() {
		return currentFile;
	}
	
	
	/**
	 * Returns the current directory.
	 * It is the directory of the current file.
	 * If there is no current file, then the current working directory will be returned.
	 */
	public File getCurrentDir() {
		if (currentFile != null) {
			return currentFile.file.getParentFile();
		}
		
		return new File(".");
	}
	
	
	/**
	 * Reads the configuration
	 */
	private void readConfiguration(Configuration conf) {
		// Load recently open files
		Configuration.Group group = conf.getGroup(CONF_RECENT_GROUP);
		String info = group.getVal("info", null);
		
		if (info != null) {
			String[] els = info.split(";");
			if (els != null) {
				for (int i = 0; i < els.length; i += 2) {
					if (els[i] != null && els[i].length() > 0) {
						int pos = Integer.parseInt(els[i + 1]);
						addRecentProject(new FileInfo(els[i], pos));
					}
				}
			}
		}
		
		// Load currently open file
		group = conf.getGroup(CONF_CURRENT_GROUP);
		String name = group.getVal("name", null);
		int pos = group.getIntVal("position", 0);
		if (name != null) {
			setCurrentFile(new FileInfo(name, pos));
		}
	}
	
	@Override
	public void save(Configuration conf) {
		// Recently open files
		Configuration.Group group = conf.getGroup(CONF_RECENT_GROUP);
		
		StringBuilder str = new StringBuilder();

		for (int i = recentFiles.size() - 1; i >= 0; i--) {
			FileInfo file = recentFiles.get(i);
			str.append(file.file.getAbsolutePath());
			str.append(';');
			str.append(file.position);
			str.append(';');
		}
		
		group.setVal("info", str.toString());

		// Currently open file
		group = conf.getGroup(CONF_CURRENT_GROUP);
		
		if (currentFile != null) {
			group.setVal("name", currentFile.file.getAbsolutePath());
			group.setVal("position", currentFile.position);
		}
		else {
			group.setVal("name", null);
		}
	}
	
	
	/**
	 * Sets the current file
	 */
	public void setCurrentFile(File file, int pos) {
		setCurrentFile(new FileInfo(file, pos));
	}
	
	/**
	 * Sets the current file
	 */
	public void setCurrentFile(FileInfo file) {
		if (file == null) {
			this.currentFile = null;
		}
		else {
			if (!file.file.exists()) {
				System.err.println("File does not exist: " + file.file);
				return;
			}
			
			this.currentFile = file;
			addRecentProject(file);
		}

		// Inform listeners about the change
		for (CurrentFileListener listener : currentFileListeners) {
			listener.currentFileChanged(currentFile.file);
		}
	}
	
	
	/**
	 * Shows an open file dialog, sets the current file, and reads its content
	 */
	public String openAndRead() {
		File file = FileUtils.openFileDialog(getCurrentDir(), "vhl", null);
		if (file == null)
			return null;
		
		setCurrentFile(new FileInfo(file, 0));
		return readCurrent();
	}
	
	
	/**
	 * Reads all text from the current file
	 */
	public String readCurrent() {
		if (currentFile == null)
			return null;
		
		// Do not open too big files
		if (currentFile.file.length() > 50000000) {
			System.err.println("File is too big: " + currentFile);
			return null;
		}

		StringBuffer text = new StringBuffer();
		BufferedReader r = null;
		try {
			r = new BufferedReader(new FileReader(currentFile.file));
			String separator = System.getProperty("line.separator");
		
			while (true) {
				String str = r.readLine();
				if (str == null)
					break;
			
				text.append(str);
				text.append(separator);
			}
			
			r.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		return text.toString();
	}
	
	
	/**
	 * Saves the given text in the current file.
	 * If there is no current file, then a file save dialog will be shown.
	 * Returns true if the text is saved.
	 */
	public boolean saveCurrent(String text, int position) {
		if (currentFile == null) {
			return saveAs(text, position);
		}
		
		currentFile.position = position;
		return saveAs(currentFile, text);
	}
	
	
	/**
	 * Shows a file save dialog and saves the text in a selected file.
	 * Returns true if the text is saved.
	 */
	public boolean saveAs(String text, int position) {
		File file = FileUtils.saveFileDialog(getCurrentDir(), "vhl", null);
		if (file == null)
			return false;
		
		return saveAs(new FileInfo(file, position), text);
	}
	
	
	/**
	 * Saves the given text in the given file and changes the current file.
	 * Returns true if the text is saved.
	 */
	private boolean saveAs(FileInfo file, String text) {
		assert(file != null);
		
		try {
			BufferedWriter w = new BufferedWriter(new FileWriter(file.file));
			w.write(text);
			w.close();
			setCurrentFile(file);
		}
		catch (Exception e) {
			e.printStackTrace();
			return false;
		}
		
		return true;
	}
	

	
	/**
	 * Adds a file to the recent projects list
	 */
	private void addRecentProject(FileInfo file) {
		if (file == null || !file.file.exists())
			return;

		// Check duplicates
		for (int i = 0; i < recentFiles.size(); i++) {
			FileInfo f = recentFiles.get(i);
			if (f.equals(file)) {
				// Move this project to the top
				recentFiles.remove(i);
				recentFiles.add(0, file);
				updateRecentMenu();
				return;
			}
		}

		// Add new file to the top
		recentFiles.add(0, file);

		// Remove older files
		if (recentFiles.size() > MAX_RECENT_FILES) {
			int n = recentFiles.size() - MAX_RECENT_FILES;
			for (int i = 0; i < n; i++) {
				// Index should be the same because elements are automatically shifted
				recentFiles.remove(MAX_RECENT_FILES);
			}
		}

		updateRecentMenu();
	}
	

	/**
	 * Updates menu of recent projects
	 */
	private void updateRecentMenu() {
		// Get the Exit item
		int n = fileMenu.getItemCount();
		int exitIndex = n;
		
		for (int i = 0; i < n; i++) {
			JMenuItem item = fileMenu.getItem(i);
			if (item != null && "Exit".equals(item.getText())) {
				exitIndex = i;
				
				// Remove all items after the Exit
				for (i += 1; i < n; i++) {
					fileMenu.remove(exitIndex + 1);
				}
			}
		}

		fileMenu.addSeparator();
		
		// Add recent files
		for (FileInfo file : recentFiles) {
			String name = file.file.getAbsolutePath();
	    	JMenuItem item = new JMenuItem(name);
	    	item.setActionCommand(CMD_FILE_RECENT + name + ";" + file.position);
	    	item.addActionListener(fileActionListener);
	    	fileMenu.add(item);
		}
	}	
}
