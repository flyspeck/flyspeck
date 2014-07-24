package util;

/**
 * Title:        KeplerConjecture 2001
 * Description:  Licensed under GNU GPL http://www.gnu.org/copyleft/gpl.html
 * Copyright:    Copyright (c) 2001, Thomas C. Hales
 * Company:
 * @author
 * @version 2001.0
 */
import java.lang.reflect.*;

/**
 * Gang of four Visitor Design Pattern.  See book "Java design Patterns"
 */
public class VisitorDefault implements Visitor {

  private Object delegate;

  /**
   * @param delegate object with some method of the form
   * void visit(<type> X).
   */
  public VisitorDefault(Visitor delegate) {
    this.delegate = delegate;
  }

  /**
   * Generic visitor.
   * Inspired by Jaroslav Tulach's trick in
   * http://www.gae.ucm.es/~fonta/ThinkingInPattersWithJava/Chapter12.html
   * and by http://www.javaworld.com/javaworld/javatips/jw-javatip98.html
   * "Reflect on the Visitor design pattern."
   * calls delegate.visit(<matching type of X> X);
   */
  public void visit(Object X) {
   try {
     Method method = getMethod(X.getClass());
     method.invoke(delegate, new Object[] {X});
   } catch (Exception e) { }
  }



  /**
   * based on "Reflect on the Visitor design pattern."
   */
  protected Method getMethod(Class c) {
   Class delegateClass = delegate.getClass();
   Class newc = c;
   Method m = null;
   // Try the superclasses
   while (m == null && newc != Object.class) {
      try {
         m = delegateClass.getMethod("visit", new Class[] {newc});
      } catch (NoSuchMethodException e) {
         //System.out.println("didn't find as " + newc.toString());
         newc = newc.getSuperclass();
      }
   }

   // Try the interfaces.
   if (newc == Object.class) {
      Class[] interfaces = c.getInterfaces();
      for (int i = 0; i < interfaces.length; i++) {
         try {
            m = delegateClass.getMethod("visit", new Class[] {interfaces[i]});
         }
         catch (NoSuchMethodException e) {
          //System.out.println("didn't find as "+interfaces[i].getName());
         }
      }
   }
   if (m == null) {
      try {
         m = delegateClass.getMethod("visit", new Class[] {Object.class});
      } catch (Exception e) {
      }
   }
   return m;
}

  /** test code starts here **/
  private static class VisitableString implements Visitable {
    private String S;
    VisitableString(String S) {
      this.S = S;
    }
    public void accept(Visitor V) {
      V.visit(this);
    }
    public String toString() {
      return S;
    }
  }
  private static class VisitableInteger implements Visitable {
    private int i;
    VisitableInteger(int i) {
      this.i = i;
    }
    public void accept(Visitor V) {
      V.visit(this);
    }
    public String toString() {
      return new Integer(i).toString();
    }
  }
  public static void main(String[] args) {
    VisitorDefault vis = new VisitorDefault(new Visitor() {
      public void visit(Object X) {
        System.out.println("unknown type: "+X.toString());
      }
      public void visit(VisitableString S) {
        System.out.println("String: "+S);
      }
      public void visit(VisitableInteger I) {
        System.out.println("Integer: "+I);
      }
      });
    Visitable[] obj = new Visitable[] {new VisitableString("hi"),new VisitableInteger(3)};
    for (int i=0;i<obj.length;i++) {
      obj[i].accept(vis);
    }
  }


}