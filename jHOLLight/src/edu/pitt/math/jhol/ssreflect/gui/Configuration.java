package edu.pitt.math.jhol.ssreflect.gui;

import java.awt.Dimension;
import java.io.File;
import java.util.ArrayList;

import org.w3c.dom.Document;
import org.w3c.dom.Node;

import static edu.pitt.math.jhol.utils.XmlDocUtils.*;

/**
 * Loads/saves configuration into a file
 */
public class Configuration {
	// Configuration file
	private File file;
	
	// The main document
	private Document doc;
	
	// Group which always returns default values
	private final static Group nullGroup = new Group(null);

	// The list of all components which save their configuration
	private final ArrayList<Saver> savers = new ArrayList<Saver>();
	
	/**
	 * Allows components to save the configuration data
	 */
	public interface Saver {
		public void save(Configuration conf);
	}
	
	
	/**
	 * A group of values
	 */
	public static class Group {
		// The corresponding xml-node
		private Node node;
		
		/**
		 * Private constructor
		 */
		private Group(Node node) {
			this.node = node;
		}
		
		/**
		 * Returns an integer value of the given attribute
		 */
		public int getIntVal(String name, int defaultValue) {
			if (node == null)
				return defaultValue;
			
			return getIntegerValue(node, name, defaultValue);
		}
		
		/**
		 * Returns a value of the given attribute
		 */
		public String getVal(String name, String defaultValue) {
			if (node == null)
				return defaultValue;

			return getValue(node, name, defaultValue);
		}
		
		/**
		 * Returns a boolean value of the given attribute
		 */
		public boolean getBoolVal(String name, boolean defaultValue) {
			if (node == null)
				return defaultValue;

			return getBooleanValue(node, name, defaultValue);
		}

		/**
		 * Returns a floating-point value of the given attribute
		 */
		public float getFloatVal(String name, float defaultValue) {
			if (node == null)
				return defaultValue;

			return getFloatValue(node, name, defaultValue);
		}
		
		/**
		 * Returns a dimension value
		 */
		public Dimension getDimensionVal(String name, int defaultWidth, int defaultHeight) {
			Dimension def = new Dimension(defaultWidth, defaultHeight);
			if (node == null)
				return def;
			
			String dim = getVal(name, null);
			if (dim == null)
				return def;

			String[] els = dim.split(",");
			if (els == null || els.length != 2)
				return def;
			
			try {
				int w = Integer.parseInt(els[0]);
				int h = Integer.parseInt(els[1]);
				
				return new Dimension(w, h);
			}
			catch (Exception e) {
				return def;
			}
		}
		
		/**
		 * Sets the value of the given attribute
		 */
		public void setVal(String name, Object value) {
			// A special treatment for dimensions
			if (value instanceof Dimension) {
				Dimension dim = (Dimension) value;
				value = "" + dim.width + "," + dim.height;
			}
			
			if (node != null)
				addAttr(node.getOwnerDocument(), node, name, value); 
		}
		
	}
	
	
	/**
	 * Creates the configuration class and loads values from the given file
	 */
	public Configuration(String fname) {
		assert(fname != null);
		file = new File(fname);
		
		try {
			if (!file.exists()) {
				doc = createNewDocument("config", 1);
			}
			else {
				doc = loadXmlFile(file);
				if (doc == null) {
					// Create a new configuration file
					doc = createNewDocument("config", 1);
				}
			}
		}
		catch (Exception e) {
			e.printStackTrace();
			doc = null;
		}
	}
	
	
	/**
	 * Gets the group described by the given path.
	 * Path should be in the form name1.name2.name3
	 */
	public Group getGroup(String path) {
		if (doc == null || path == null || path.length() == 0)
			return nullGroup;
		
		String[] els = path.split("\\.");
		if (els == null || els.length == 0) {
			els = new String[] { path };
		}
		
		Node node = doc.getFirstChild();
		for (int i = 0; i < els.length; i++) {
			String el = els[i];
			if (el == null || el.length() == 0)
				return nullGroup;
			
			Node next = getChildByTagName(node, el);
			if (next == null) {
				// Create the missing node
				next = doc.createElement(el);
				node.appendChild(next);
			}
			
			node = next;
		}
		
		return new Group(node);
	}
	
	
	/**
	 * Adds the saver
	 */
	public void addSaver(Saver saver) {
		savers.add(saver);
	}
	
	/**
	 * Removes the saver
	 */
	public void removeSaver(Saver saver) {
		savers.remove(saver);
	}

	
	/**
	 * Updates and saves the configuration
	 */
	public void updateAndSave() throws Exception {
		if (file == null || doc == null)
			return;
		
		// Update the data
		for (Saver saver : savers) {
			saver.save(this);
		}
		
		// Save the data
		saveDocument(doc, file);
	}
}
