/**
 * Copyright (c) 2001, Thomas C. Hales
 * Software that reads a properties file.
 * Modified from GNU GPL code in the webmacro package distributed by Semiotek, Inc.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * A copy of the GNU General Public License
 * is available at http://www.gnu.org/copyleft/gpl.html.
 * For a printed copy, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
**/

package util;

import java.io.*;
import java.util.*;

/**
  * Config represents the data stored in a *.properties file, and
  * a few things that can be derived from it;
  * <p>
  * You can put your own variables into the configuration file, and use
  * Config to access them. The configuration file is composed of key
  * value pairs separated by an "=". It can contain comments, which are
  * lines beginning with "#".
  * <p>
  * When using a Config object, you should refer to standard values in the
  * config file by way of the string constants.
  */

public class Config
{
   /**
     * Can override this through a constructor-supplied filename.
     */
   final private static String CONFIG_FILE = "config.properties";

   /**
     * Internally configuration information is stored as a Properties
     * object, here it is.
     */
   private Properties myProps;

   /**
     * Construct a new config file, reading from the default location.
     */
   public Config() throws Exception {
      this(CONFIG_FILE);
   }

   public Config(String configFile) throws Exception {
      loadProperties(getStream(configFile));
   }

   /**
    * Read config from the supplied input stream
    */
   public Config(InputStream configStream) throws Exception {
      loadProperties(configStream);
   }

   private final String errorMessage = "Config: UNABLE TO LOAD CONFIGURATION:\n"
               + "config.properties file should be located somewhere "
               + "on the same classpath as was used to load the core  "
               + "classes. It is usually called \"config.properties\", "
               + "though your application may have specified another name.";

   /**
     * @param InputStream containing properties data.
     */
   private void loadProperties(InputStream configStream) throws Exception {
      Properties p = new Properties();
      try {
         p.load(configStream);
         configStream.close();
      }
      catch (Exception e) {
         throw new Exception(errorMessage);
      }
      finally {
        myProps = p;
      }
   }

   /**
    * @param file located through the class loader or as a FileInputStream.
    */
   private InputStream getStream(String file) throws Exception {
         Class c = Config.class;
         InputStream in = c.getResourceAsStream(file);
         if (null == in) {
            c = Class.class;
            in = c.getResourceAsStream(file);
         }
         if (null == in) {
            in = new FileInputStream(file);
         }
         return in;
   }


   /**
     * Look up the specified configuration property in the config file
     * and return the value assigned to it. If it does not exist, return null.
     * @param configProperty the variable keyword (left hand side)
     * @return the value corresponding to the keyword (right hand side)
     */
   final public String get(String configProperty) {
      String ret = myProps.getProperty(configProperty);
      return (ret==null ? "" : ret.trim() );
   }

   final public boolean getBooleanProperty(String name,boolean defaultValue) {
      String prop = this.get(name);
      if (prop==null) return defaultValue;
      return Boolean.valueOf(prop).booleanValue();
    }

    final public int getIntProperty(String name,int defaultValue) {
      String prop = this.get(name);
      if (prop.equalsIgnoreCase("")) return defaultValue;
      return Integer.valueOf(prop).intValue();
    }

   /**
    * true if propValue is "yes" or "true"
    */
   final public static boolean isTrue(String propValue) {
      return ((propValue != null) &&
            ((propValue.equalsIgnoreCase("yes")) ||
              propValue.equalsIgnoreCase("true")));
   }


   /**
     * Return the configuration properties object
     */
   final public Properties getProperties() {
      return myProps;
   }

   public static void main(String args[]) {
    try {
      Config config = new Config("test.properties");
      String prop = config.get("testvalue");
      System.out.println(prop);
    }
    catch (Exception e) {
      System.out.println("not found");
    }
   }


}

