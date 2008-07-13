package util;


/**
 * Title:        Graph00
 * Description:
 * Copyright:    Copyright (c) Thomas C. Hales
 * Company:      University of Michigan
 * @author Thomas C. Hales
 * @version 1.0
 */


public class CalendarExtension extends java.util.GregorianCalendar {

  public long toLong() {
    return super.getTimeInMillis();
  }
  public double seconds() {
    return ((double) toLong())/1000.0;
  }
  public double secondGap(CalendarExtension c) {
    return this.seconds()-c.seconds();
  }
  public CalendarExtension() {
    super();
  }

}