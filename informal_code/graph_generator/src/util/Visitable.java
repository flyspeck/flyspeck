package util;

/**
 * Title:        KeplerConjecture 2001
 * Description:  Licensed under GNU GPL http://www.gnu.org/copyleft/gpl.html
 * Copyright:    Copyright (c) 2001, Thomas C. Hales
 * Company:
 * @author
 * @version 2001.0
 */

/**
 * Gang of Four Visitor design pattern.  See book "Java Design Patterns"
 */
public interface Visitable {

  /**
   * The implementation should always be a single line of code:
   *  visitor.visit(this);
   */
  void accept(Visitor visitor);

}