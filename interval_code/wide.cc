/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 2011-05-19                                                     */
/* ========================================================================== */
 
//  Calculation of derivatives of tau as a locally constant function.

/*

By the locally constant approximation of a function f we mean
the Function whose derivatives and second derivatives are identically
zero and whose constant term is a fat interval spanning the min and max of f.

When we use the locally constant approximation we are required to
turn off the (allowDerivatives) option.  (Even though the locally constant
function is weakly monotonic, the locally constant approximation of the
boundary face does not contain in general the optimal value over the entire cell.)


 */

#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
#include <assert.h>
#include <float.h>
}
#include "error.h"
#include "interval.h"
#include "univariate.h"
#include "lineInterval.h"
#include "wide.h"



static interval delta(interval x1,interval x2,interval x3,interval x4,interval x5,
			interval x6) {
  /*
    This code is used to give a proof of a specific inequality on a specific domain.
    As preconditions we have that delta_x is
    - decreasing in x4.
    - increasing in x2,x3,x5,x6.
    - unknown in x1.
    delta_x is quadratic with neg. leading coeff. in each var.
   */
  // lower endpoints,
  interval t;
  interMath::down();
  {
  double z1a = x1.lo;
  double z1b = x1.hi;
  double z2 = x2.lo;
  double z3 = x3.lo;
  double z4 = x4.hi;
  double z5 = x5.lo;
  double z6 = x6.lo;
  double c0 = (-z2)*z3*z4 + (- z4)*z5*z6 + z3*(z2 - z3 + z4 + z5 - z6)*z6 + 
    z2*z5*(-z2 + z3 + z4 - z5 + z6);
  double c1 = z2*z5 + (- z3)*z5 + (- z2)*z6 + z3*z6 + 
    z4*(z2 + z3 - z4 + z5 + z6);
  double c2 = - z4;
  t.lo = min(c0 + c1*z1a + c2*z1a*z1a,c0 + c1*z1b + c2 * z1b * z1b);
  }
  interMath::up();
    {
  double z1a = x1.lo;
  double z1b = x1.hi;
  double z2 = x2.hi;
  double z3 = x3.hi;
  double z4 = x4.lo;
  double z5 = x5.hi;
  double z6 = x6.hi;
  double c0 = (-z2)*z3*z4 + (- z4)*z5*z6 + z3*(z2 - z3 + z4 + z5 - z6)*z6 + 
    z2*z5*(-z2 + z3 + z4 - z5 + z6);
  double c1 = z2*z5 + (- z3)*z5 + (- z2)*z6 + z3*z6 + 
    z4*(z2 + z3 - z4 + z5 + z6);
  double c2 = - z4;
  t.hi = max(c0 + c1*z1a + c2*z1a*z1a,c0 + c1*z1b + c2 * z1b * z1b);
  if (0==c2 ) { throw unstable::x; }
  double crit_lo = - (c1/(2.0*c2));
  double crit_hi = c1/(-2.0 * c2);
  if (crit_hi < crit_lo) { error::fatal("critical point inversion in delta max"); }
  double tcrit;
  if (crit_lo <= z1b && crit_hi >= z1a) {
    // z1a and z1b are pos, c2 neg, c1 pos.
    tcrit = c0 + (c1*c1)/(-4.0 * c2);
    t.hi = max(t.hi,tcrit);
  }
  }
    return t;
}

interval wide::delta_y(const domain& zn,const domain& zu) {
  interval y;
  interval x[6];
  for (int i=0;i<6;i++) { y.lo = zn.getValue(i); y.hi = zu.getValue(i); x[i]=y*y; }
  return  delta(x[0],x[1],x[2],x[3],x[4],x[5]);
}









/***************************************************
 ** TEST CODE
 ***************************************************/


static int barelyLess(double x,double y,double epsilon)
{
  if ((x>y)||(y>x+epsilon))
    {
      cout << "barelyLess " << x << " " << y << endl << flush;
      return 0;
    }
  return 1;
}

void wide::selfTest() {
  cout << " -- loading wide routines " << endl << flush;
  /* test delta */ {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  interval x[6] = {"4.1","4.2","4.3","4.4","4.5","4.6"};  
  interval d = delta(x[0],x[1],x[2],x[3],x[4],x[5]);
  double v = 163.677;
  if  (barelyLess(d.lo,v,eps) && barelyLess(v,d.hi,eps)) { } else { error::fatal("wide delta"); }
    }

  /* test deltamax */ {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  interval x[6] = {"4.1","4.2","4.3","4.4","4.5","4.6"};  
  x[0].hi = 10.0;
  interval d = delta(x[0],x[1],x[2],x[3],x[4],x[5]);
  double vlo = 140.3719999999999;
  double vhi = 191.20200568181824;
  if  (barelyLess(d.lo,vlo,eps) && barelyLess(vhi,d.hi,eps)) { } else { error::fatal("wide delta max"); }
    }
}

