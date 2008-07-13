
/**
 * Title:        Linear Programming Stuff<p>
 * Description:  Kepler conjecture related linear programming.<p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      (none)<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package util;

//: com:bruceeckel:test:RunUnitTests.java
// Discovering the inner unit test
// class and running each test.
//package com.bruceeckel.test;
import java.lang.reflect.*;
import java.util.Iterator;

public class RunUnitTests {
  public static void
  require(boolean requirement, String errmsg) {
    if(!requirement) {
      System.err.println(errmsg);
      System.exit(1);
    }
  }

  public static void main(String[] args) {
    require(args.length > 0,
      "Usage: RunUnitTests qualified-class-list");
    for (int i=0;i<args.length;i++)
      run(args[i]);
    }

  public static void run(String arg) {

    try {
      Class c = Class.forName(arg);
      // Only finds the inner classes
      // declared in the current class:
      Class[] classes = c.getDeclaredClasses();
      Class ut = null;
      for(int j = 0; j < classes.length; j++) {
        // Skip inner classes that are
        // not derived from UnitTest:
        if(!UnitTest.class.
            isAssignableFrom(classes[j]))
              continue;
        ut = classes[j];
        break; // Finds the first test class only
      }
      require(ut != null,
        "No inner UnitTest class found in "+c.getName());
      require(
        Modifier.isPublic(ut.getModifiers()),
        "UnitTest class must be public");
      require(
        Modifier.isStatic(ut.getModifiers()),
        "UnitTest class must be static");
      Method[] methods = ut.getDeclaredMethods();
      for(int k = 0; k < methods.length; k++) {
        Method m = methods[k];
        // Ignore overridden UnitTest methods:
        if(m.getName().equals("cleanup"))
          continue;
        // Only public methods with no
        // arguments and void return
        // types will be used as test code:
        if(m.getParameterTypes().length == 0 &&
           m.getReturnType() == void.class &&
           Modifier.isPublic(m.getModifiers())) {
             // The name of the test is
             // used in error messages:
             UnitTest.testID = m.getName();
             // A new instance of the
             // test object is created and
             // cleaned up for each test:
             Object test = ut.newInstance();
             m.invoke(test, new Object[0]);
             ((UnitTest)test).cleanup();
        }
      }
    } catch(Exception e) {
      e.printStackTrace(System.err);
      // Any exception will return a nonzero
      // value to the console, so that
      // 'make' will abort:

      System.exit(1);
    }
    // After all tests in this class are run,
    // display any results. If there were errors,
    // abort 'make' by returning a nonzero value.
    if(UnitTest.errors.size() != 0) {
      Iterator it = UnitTest.errors.iterator();
      while(it.hasNext())
        System.err.println(it.next());
      System.exit(1);
    }
    else System.err.println("No errors found in "+arg);
  }
} ///:~
