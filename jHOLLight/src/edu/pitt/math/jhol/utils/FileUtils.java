package edu.pitt.math.jhol.utils;

import java.awt.Window;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;

import javax.swing.JFileChooser;
import javax.swing.filechooser.FileFilter;

/**
 * Utilities for working with files
 */
public class FileUtils {
	/* Base directory for file operations */
	private static File baseDir = null;
	
	
	/**
	 * Sets the base directory for file operations
	 * @param baseDir
	 */
	public static void setBaseDir(File baseDir) {
		if (!baseDir.exists()) {
			return;
		}
		
		FileUtils.baseDir = baseDir;
	}
	
	
	/**
	 * Appends the base directory to the given file name
	 * @param fname
	 * @return
	 */
	public static File getFile(String fname) {
		File file = new File(fname);
		if (baseDir != null) {
			if (!file.isAbsolute()) {
				file = new File(baseDir, fname);
			}
		}
		
		return file;
	}
	

	/**
	 * Creates a new file with the given name or erases an existing file
	 * @param name
	 */
	public static void createNew(String name) {
		File file = new File(name);
		if (baseDir != null) {
			if (!file.isAbsolute()) {
				file = new File(baseDir, name);
			}
		}
		
		try {
			if (!file.exists()) {
				file.createNewFile();
			}
			else {
				if (file.isFile()) {
					if (file.delete())
						file.createNewFile();
				}
			}
			
		}
		catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Creates a new file with a unique name and with the given prefix
	 * @param name
	 */
	public static String createUniqueNew(String prefix) {
		String name = prefix;
		int counter = 2;

		File output;
		if (baseDir != null) {
			output = baseDir;
		}
		else {
			output = new File(".");
		}
		
		try	{
			while (true) {
				File file = new File(output, name);
			
				if (file.exists()) {
					name = prefix + counter;
					counter++;
				}
				else {
					file.createNewFile();
					break;
				}
			}
		}
		catch (IOException e) {
			e.printStackTrace();
			return null;
		}
		
		return name;
	}
	
	
	/**
	 * Returns all files satisfying the given filter in the given directory
	 * and its sub-directories
	 * @param directory
	 * @param filter
	 * @param recurse
	 * @return
	 */
	public static ArrayList<File> findAllFiles(File directory, FilenameFilter filter, boolean recurse) {
		ArrayList<File> files = new ArrayList<File>();
		
		// Get files / directories in the directory
		File[] entries = directory.listFiles();
			
		// Go over entries
		for (File entry : entries)
		{
				// If there is no filter or the filter accepts the 
				// file / directory, add it to the list
				if (filter == null || filter.accept(directory, entry.getName()))
				{
					files.add(entry);
				}
				
				// If the file is a directory and the recurse flag
				// is set, recurse into the directory
				if (recurse && entry.isDirectory())
				{
					files.addAll(findAllFiles(entry, filter, recurse));
				}
		}
			
		return files;
	}
	
	
	/**
	 * Splits the given file path into a list of all parent directories
	 * starting from the root
	 * @param file
	 * @return
	 */
	public static ArrayList<String> splitFilePath(File file) {
		ArrayList<String> result = new ArrayList<String>();

		while (file != null) {
			result.add(file.getName());
			file = file.getParentFile();
		}
		
		// Reverse the resulting list
		int n = result.size();
		for (int i = 0; i < n / 2; i++) {
			String tmp = result.get(i);
			result.set(i, result.get(n - i - 1));
			result.set(n - i - 1, tmp);
		}
		
		return result;
	}
	

	/**
	 * Returns a relative path to the given file
	 * @param file
	 * @return
	 */
	public static String getRelativePath(File base, File file) {
		if (file == null)
			return null;
		
		if (base == null)
			return file.getAbsolutePath();
		
		if (base.isFile())
			base = base.getParentFile();

		// Get canonical paths
		File canonicalBase;
		File canonicalFile;
		
		try {
			canonicalBase = new File(base.getCanonicalPath());
			canonicalFile = new File(file.getCanonicalPath());
		}
		catch (Exception e) {
			e.printStackTrace();
			return file.getAbsolutePath();
		}
		
		ArrayList<String> baseList = splitFilePath(canonicalBase);
		ArrayList<String> fileList = splitFilePath(canonicalFile);

		int bn = baseList.size();
		int fn = fileList.size();
		int counter = 0;
		
		// Skip all common base directories
		while (true) {
			if (counter >= bn || counter >= fn)
				break;

			String name1 = baseList.get(counter);
			String name2 = fileList.get(counter);
			
			if (!name1.equals(name2))
				break;
			
			counter++;
		}

		StringBuilder str = new StringBuilder();
		for (int i = counter; i < bn; i++) {
			str.append("..");
			str.append("/");
		}
		
		for (int i = counter; i < fn; i++) {
			str.append(fileList.get(i));
			if (i < fn - 1)
				str.append("/");
		}
		
		return str.toString();
	}
	

	/**
	 * Returns file's extension
	 * @param f
	 * @return
	 */
	public static String getExtension(File f) {
		return getExtension(f.getName());
	}
	

	/**
	 * Returns file's extension
	 * @param fname
	 * @return
	 */
	public static String getExtension(String fname) {
		String ext = "";
		int i = fname.lastIndexOf('.');

		if (i > 0 && i < fname.length() - 1) {
			ext = fname.substring(i + 1).toLowerCase();
		}
		
		return ext;
	}

	
	/**
	 * Creates a file chooser for the given file extension
	 * @param dir
	 * @param extension
	 * @return
	 */
	public static JFileChooser createFileChooser(File dir, final String extension) {
		final JFileChooser fc = new JFileChooser(dir);
		
		fc.setFileFilter(new FileFilter() {
			// Accept all directories and all files with the given extension
			public boolean accept(File f) {
				if (f.isDirectory()) {
					return true;
				}

				if (extension == null)
					return true;
				
				String ext = getExtension(f);
				if (ext != null) {
					if (ext.equals(extension))
						return true;
					else
						return false;
				}

				return false;
			}

			// The description of this filter
			public String getDescription() {
				if (extension == null)
					return "*.*";
				
				return "*." + extension;
			}
		});

		return fc;
	}
	
	
	/**
	 * Shows an open file dialog and returns a selected file
	 * @return
	 * @throws Exception
	 */
	public static File openFileDialog(File dir, String extension, Window parent) {
		JFileChooser fc = createFileChooser(dir, extension);
		int returnVal = fc.showOpenDialog(parent);
		
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			File file = fc.getSelectedFile();
			return file;
		}
		
		return null;
	}
	
	
	
	/**
	 * Shows an open file dialog and returns a selected file
	 * @return
	 * @throws Exception
	 */
	public static File saveFileDialog(File dir, final String extension, Window parent) {
		JFileChooser fc = createFileChooser(dir, extension);
		int returnVal = fc.showSaveDialog(parent);
		
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			File file = fc.getSelectedFile();
			return file;
		}
		
		return null;
	}

}
