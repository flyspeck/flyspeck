
/**
 * Title:        Linear Programming Stuff<p>
 * Description:  Kepler conjecture related linear programming.<p>
 * Copyright:    Copyright (c) Thomas C. Hales
 * @author Thomas C. Hales
 * @version 1.0
 */
package util;

import java.util.ArrayList;


//
// The basic unit testing class
//package com.bruceeckel.test;

/**
 * Unit test is based on code located at
 * http://www.gae.ucm.es/~fonta/ThinkingInPattersWithJava/Chapter02.html
 * com:bruceeckel:test:UnitTest.java.
 * <p>
 */

public class UnitTest {
  static String testID;
  static ArrayList errors = new ArrayList();

  /**
   * Override cleanup() if test object creation allocates non-memory
   * resouces that must be cleaned up.
   */
  protected void cleanup() {}

  /**
   * Verify the truth of  a condition.
   */
  protected final void jassert(boolean condition){
    if(!condition) {
      errors.add("failed: " + testID);
      new Exception().printStackTrace();
      }
  }

  protected final void jassert(boolean condition,String message) {
    if (!condition) {
      errors.add("failed: " + testID+" "+message);
      new Exception().printStackTrace();
    }
  }

}

