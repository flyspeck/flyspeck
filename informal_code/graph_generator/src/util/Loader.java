/**
 ** Grinding Java Dynamic Java Written by Shai Almog
 *  Downloaded and moved into util package by Thomas C. Hales, January 2001.
 *  originally called MacroExtension.java
 */
package util;

import sun.tools.javac.Main;
import java.util.*;
import java.io.*;

/**
 * To use the Loader you simply add it to your program
 * and add an interface for selecting the macro, then use the simple
 * methods of this class to compile and execute a macro.
 * The class offers several features:
 * 1. Interaction with your application.
 * 2. The full power you had writing the application will be available
 *    to your users.
 * 3. You can add a sandbox to block some functionality.
 * 4. You can ship upgrades/fixes as plugins.
 * 5. Other vendors and users can easily write plugins.
 * 6. Plugins will be fully integrate, cross platform and run in the
 *    same speed as the VM.
 * It is recommended you expose some of your software's internals
 * to your users to make this tool more effective.
**/

public class Loader extends ClassLoader
{
  public Loader()
  {
    compilerClass = new sun.tools.javac.Main(System.out,"javac");
  }

  /**
   * This method accepts a class file as parameter
   * and returns an instance of it.
  **/
  public Object getObject(String fileName)
    throws  java.lang.ClassNotFoundException,
            java.lang.InstantiationException,
            java.lang.IllegalAccessException
  {
    Class classInstance = getClass();
    return(classInstance.forName(fileName).newInstance());
  }

  /**
   * This method accepts a java file as parameter and compiles it.
   * It returns true if compilation was successful and false otherwise.
  **/
  public boolean compile(String fileName)
  {
    String [] stringArr = new String[1];
    stringArr[0] = fileName;
    return(compilerClass.compile(stringArr));
  }

  /**
   * The main method is conveniently located here for testing purposes.
  **/
  public static void main(String argv[])
  {
    Loader m = new Loader();
    m.compile("HelloWorld.java");
    m.loadObject("HelloWorld");
  }

  /**
   * creates an instance of a class by getting its name
   * and returns that instance, or null if none were found.
  **/
  public Object loadObject(String className)
  {
    try
    {
      loadClass(className, true);
      return(getObject(className));
    }
    catch(java.lang.ClassNotFoundException e)
    {
      System.out.println("Class not found exception: " + e.getMessage());
    }
    catch(java.lang.InstantiationException e)
    {
      System.out.println("Instantiation exception: " + e.getMessage());
    }
    catch(java.lang.IllegalAccessException e)
    {
      System.out.println("Illegal access exception : " + e.getMessage());
    }
    catch(Exception e)
    {
      System.out.println("An exception was thrown: " + e.getMessage());
    }
    return(null);
  }


  protected Class loadClass(String className, boolean callReslove)
  {
    Class returnValue = (Class) classCache.get(className);

    if(returnValue != null)
      return(returnValue);

    String classFullName;

    try
    {
      File classFile;
      if (!className.endsWith(".class"))
        classFullName = className + ".class";
      else
      {
        className = className.substring(0, className.length() - 5);
        System.out.println("Class name is: " + className);
        classFullName = className + ".class";
      }

      classFile = new File(classFullName);

      FileInputStream inFile = new FileInputStream(classFile);
      byte[] classData = new byte[(int)classFile.length()];

      inFile.read(classData);

      inFile.close();

      returnValue = defineClass(className, classData, 0, classData.length);

      classCache.put(className, returnValue);
    }
    catch(IOException ioerr)
    {
      try
      {
        returnValue = findSystemClass(className);
        return(returnValue);
      }
      catch (Exception anyException)
      {
        System.out.println("File access error: " + anyException.getMessage());
        return(null);
      }
    }

    if(callReslove)
    {
      resolveClass(returnValue);
    }

    return(returnValue);
  }

  /**
   * Notice the long name. It's here to avoid namespace
   * problems with another Main
   **/
  private sun.tools.javac.Main compilerClass;
  private Hashtable classCache = new Hashtable();
}
