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

static interval zero("0.0");
static interval one("1.0");
static interval two("2.0");
static interval four ("4.0");
static interval eight ("8.0");
static interval half ("0.5");
static interval pi("3.14159265358979323846264338328");
static interval c1("0.175479656091821810512566677667"); // sol0/pi.
static interval c052("0.52");

// adapted from lineInterval.cc
static interval U(interval x1,interval x2,interval x6)
	{
	  return (-x1)*x1+(-x2)*x2+(-x6)*x6+two*(x1*x2+x2*x6+x6*x1);
	}

static interval DUa(interval x1,interval x2,interval x6)
	{
	  return two* (- x1 + x2 + x6);
	}

static interval rho(interval y1) {
  return one + c1 * (y1 - two)/c052;
}

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

//debug

static int counter = 0;


void show(const interval y,const char* s) {
  if (counter % 500000 == 300) {
  cout << s << ": " << y.lo << " " << y.hi << endl;
  }
}

void showr(const interval y,const char* s) {
    cout << s << ": " << y.lo << " " << y.hi << endl;
}

void   report_values(const interval y1,const interval y2,const interval y3,
		     const interval y4,const interval y5,const interval y6,
		     const interval mdtau,const interval mdtau2uf) {
  if (counter++ % 5000000 == 100) {
    showr(y1,"y1");
    showr(y2,"y2");
    showr(y3,"y3");
    showr(y4,"y4");
    showr(y5,"y5");
    showr(y6,"y6");
    showr(mdtau,"mdtau");
    showr(mdtau2uf,"mdtau2uf");
  }
}

// never called, because version computed and cached in mdtau2uf is used.

interval mdtau(const interval y1,const interval y2,const interval y3,const interval y4,const interval y5,const interval y6) {
  interval x1=y1*y1;
  interval x2 = y2*y2;
  interval x3 = y3*y3;
  interval x4 = y4*y4;
  interval x5 = y5*y5;
  interval x6 = y6*y6;

  interval chain = two*y1;  // D[x1,y1].
  interval Pchain = two;
  interval chain2 = four* x1;

  interval u135 = U(x1,x3,x5);
  interval u126 = U(x1,x2,x6);
  interval u234 = U(x2,x3,x4);

  interval uf = four*u135*u126*u234*y1*y2*y3;
  interval du135 = DUa(x1,x3,x5);
  interval du126 = DUa(x1,x2,x6);
  show(y1,"y1"); show(y2,"y2"); 
  show(y1,"y3"); show(y2,"y4"); 
  show(y1,"y5"); show(y2,"y6"); 
  show(u135,"u135"); show(u126,"u126"); show(u234,"u234");

  if (u234.lo <= 0.0 || u135.lo <= 0.0 || u126.lo <= 0.0) { throw unstable::x; }

  interval Luf = (du135/u135 + du126/u126 )*chain + one/y1;
  show(uf,"uf"); show(du135,"du135"); show(du126,"du126"); show(Luf,"Luf");

  interval n4 = x2*x3 + x1*x4 - x2*x5 - x3*x6 + x5*x6 - 
    x1*(-x1 + x2 + x3 - x4 + x5 + x6); // - del4
  interval del4 = -n4;
  if (del4.hi >= 0.0) { throw unstable::x; }

  interval n5 = x1*x3 - x1*x4 + x2*x5 - x3*x6 + x4*x6 - 
    x2*(x1 - x2 + x3 + x4 - x5 + x6);  // - del5

  interval n6 = x1*x2 - x1*x4 - x2*x5 + x4*x5 - 
    x3*(x1 + x2 - x3 + x4 + x5 - x6) + x3*x6; // - del6

  interval Dn4 = two*x1 - x2 - x3 + two*x4 - x5 - x6;

  interval del = delta(x1,x2,x3,x4,x5,x6);

  interval del1 = -(x1*x4) + x2*x5 - x3*x5 - x2*x6 + x3*x6 +
   x4*(-x1 + x2 + x3 - x4 + x5 + x6);

  interval del2 = x1*x4 - x3*x4 - x2*x5 - x1*x6 + 
    x3*x6 + x5*(x1 - x2 + x3 + x4 - x5 + x6);

  interval del3 = x1*x4 - x2*x4 - x1*x5 + x2*x5 - 
    x3*x6 + (x1 + x2 - x3 + x4 + x5 - x6)*x6;

  interval Pdel = del1 * chain;

 show(n4,"n4"); show(n5,"n5"); show(n6,"n6");
  show(Dn4,"Dn4"); show(del,"del"); show(del1,"del1"); show(del2,"del2"); 
  show(del3,"del3"); show(Pdel,"Pdel"); 

  interval sd4 = four*x1*del;
  interval sd5 = four*x2*del;
  interval sd6 = four*x3*del;

  interval Dsd4 = four*del + four*x1*del1;

  interval m4diff = two*Dn4*sd4 - n4* Dsd4;
  interval m4 = m4diff*chain*u234*y2*y3;
  interval m5 = -four*x2*u234*del3*two*x1*u135*y3;
  interval m6 = -four*x3*u234*del2*two*x1*u126*y2;

  interval rhoy1 = rho(y1);
  interval rhoy2 = rho(y2);
  interval rhoy3 = rho(y3);
  interval Prhoy1 = c1/c052;
  show(sd4,"sd4"); show(sd5,"sd5"); show(sd6,"sd6");
  show(Dsd4,"Dsd4"); show(m4diff,"m4diff"); show(m4,"m4");
  show (m5,"m5"); show(m6,"m6"); show(c1,"const1"); show(rhoy1,"rhoy1");
  show(rhoy2,"rhoy2"); show(rhoy3,"rhoy3"); show(Prhoy1,"Prhoy1");


  interval rr = rhoy1 * m4 + rhoy2 * m5 + rhoy3 * m6;
  
  interval term1 = Prhoy1 * pi * interMath::sqrt(del);
  interval t = interMath::sqrt(four * x1)/del4;
  interval t2 = t*t;
  interval term2a = del * t * univariate::matan(t2 *del);
  interval term2 = term2a * Prhoy1;
  interval term3 = rr/uf;
  show(rr,"rr"); 
  show(t,"t"); show(t2,"t2"); show(term2a,"term2a");
  show(term1,"term1"); 
  show(term2,"term2"); 
  show(term3,"term3");

  return term1+term2+term3;
};

// backup values;
static interval y1b=zero;
static interval y2b=zero;
static interval y3b=zero;
static interval y4b=zero;
static interval y5b=zero;
static interval y6b=zero;
static interval mdtaub=zero;
static interval mdtau2ufb=zero;


// most of the code is identical to mdtau.

void set_mdtau2uf(const interval y1,const interval y2,const interval y3,const interval y4,const interval y5,const interval y6) {
  interval x1=y1*y1;
  interval x2 = y2*y2;
  interval x3 = y3*y3;
  interval x4 = y4*y4;
  interval x5 = y5*y5;
  interval x6 = y6*y6;

  interval chain = two*y1;  // D[x1,y1].
  interval Pchain = two;
  interval chain2 = four* x1;

  interval u135 = U(x1,x3,x5);
  interval u126 = U(x1,x2,x6);
  interval u234 = U(x2,x3,x4);

  interval uf = four*u135*u126*u234*y1*y2*y3;
  interval du135 = DUa(x1,x3,x5);
  interval du126 = DUa(x1,x2,x6);
  show(y1,"y1"); show(y2,"y2"); 
  show(y3,"y3"); show(y4,"y4"); 
  show(y5,"y5"); show(y6,"y6"); 
  show(u135,"u135"); show(u126,"u126"); show(u234,"u234");

  if (u234.lo <= 0.0 || u135.lo <= 0.0 || u126.lo <= 0.0) { throw unstable::x; }

  interval Luf = (du135/u135 + du126/u126 )*chain + one/y1;
  show(uf,"uf"); show(du135,"du135"); show(du126,"du126"); show(Luf,"Luf");

  interval n4 = x2*x3 + x1*x4 - x2*x5 - x3*x6 + x5*x6 - 
    x1*(-x1 + x2 + x3 - x4 + x5 + x6); // - del4
  interval del4 = -n4;
  if (del4.hi >= 0.0) { throw unstable::x; }

  interval n5 = x1*x3 - x1*x4 + x2*x5 - x3*x6 + x4*x6 - 
    x2*(x1 - x2 + x3 + x4 + (x6- x5) );  // - del5

  interval n6 = x1*x2 - x1*x4 - x2*x5 + x4*x5 - 
    x3*(x1 + x2 - x3 + x4 + (x5 - x6)) + x3*x6; // - del6

  interval Dn4 = two*x1 - x2 - x3 + two*x4 - x5 - x6;

  interval del = delta(x1,x2,x3,x4,x5,x6);

  interval del1 = (x2 - x3)*(x5-x6) +
   x4*(- two*x1 + x2 + x3 - x4 + x5 + x6);

  interval del2 = x1*x4 - x3*x4 - x2*x5 - x1*x6 + 
    x3*x6 + x5*(x1 - x2 + x3 + x4 - x5 + x6);

  interval del3 = x1*x4 - x2*x4 + (x2-x1)*x5 
     + (x1 + x2 - two*x3 + x4 + x5 - x6)*x6;

  interval Pdel = del1 * chain;

 show(n4,"n4"); show(n5,"n5"); show(n6,"n6");
  show(Dn4,"Dn4"); show(del,"del"); show(del1,"del1"); show(del2,"del2"); 
  show(del3,"del3"); show(Pdel,"Pdel"); 

  interval sd4 = four*x1*del;
  interval sd5 = four*x2*del;
  interval sd6 = four*x3*del;

  interval Dsd4 = four*del + four*x1*del1;

  interval m4diff = two*Dn4*sd4 - n4* Dsd4;

  // m4diff1 == m4diff. not used.
  interval m4diff1 = four * del * (two * x1 * Dn4 - n4) - n4 * four * x1 * del1;

  interval m4 = m4diff*chain*u234*y2*y3;
  interval m5 = -four*x2*u234*del3*two*x1*u135*y3;
  interval m6 = -four*x3*u234*del2*two*x1*u126*y2;

  interval rhoy1 = rho(y1);
  interval rhoy2 = rho(y2);
  interval rhoy3 = rho(y3);
  interval Prhoy1 = c1/c052;
  show(sd4,"sd4"); show(sd5,"sd5"); show(sd6,"sd6");
  show(Dsd4,"Dsd4"); show(m4diff,"m4diff"); 
  show(m4diff1,"m4diff1"); show(m4,"m4");
  show (m5,"m5"); show(m6,"m6"); show(c1,"const1"); show(rhoy1,"rhoy1");
  show(rhoy2,"rhoy2"); show(rhoy3,"rhoy3"); show(Prhoy1,"Prhoy1");

  interval rr1 = u234 * y2 *y3 * (rhoy1 * m4diff * chain 
				  - (four * two * x1 ) * (rhoy2 * y2 * del3 * u135 +
								 rhoy3 * y3 * del2 * u126));
  interval rr = rhoy1 * m4 + rhoy2 * m5 + rhoy3 * m6;
  show(rr,"rr"); 
  show(rr1,"rr1");

  rr.lo = max (rr.lo,rr1.lo); rr.hi = min(rr.hi,rr1.hi);
  if (rr.lo > rr.hi) { error::message("rr inverted"); }
  show(rr,"rr");
  // the code is the same as mdtau up to here.

  interval term1 = Prhoy1 * pi * interMath::sqrt(del);
  interval t = interMath::sqrt(four * x1)/del4;
  interval t2 = t*t;
  interval term2a = del * t * univariate::matan(t2 *del);
  interval term2 = term2a * Prhoy1;
  interval term3 = rr/uf;
  interval mdtau= term1+term2+term3;

  show(t,"t"); show(t2,"t2"); show(term2a,"term2a");
  show(term1,"term1"); 
  show(term2,"term2"); 
  show(term3,"term3");
  show(mdtau,"mdtau");

  // start variation in code here.

  // WARNING: EMBEDDED ASSUMPTION HERE THAT del is on the domain del>=15.
  // mdtau2uf is used in just one inequality: 5556646409.
  static interval ft = "15.0";
  del.lo  =  max (del.lo,ft.lo);
  del.hi  =  max (del.hi,ft.hi);
  // Also uf >= when delta>=0, and we compute mdtau2uf == mdtau2 * uf
  // END: EMBEDDED ASSUMPTION.

    if (del.lo <= 0.0 || uf.lo <= 0.0) { throw unstable::x; }
  interval Ldel = Pdel / del;
  interval D2n4 = two;
  interval D2sd4 = -eight*x1*x4 + eight*(-(x1*x4) + x2*x5 - x3*x5 - x2*x6 + x3*x6 + 
			       x4*(-x1 + x2 + x3 - x4 + x5 + x6));
  interval Dm4diff = two * D2n4 * sd4 + Dn4 * Dsd4 - n4 *D2sd4;
  interval Pm4 = (Dm4diff * chain2 + m4diff * Pchain ) * u234 * y2 * y3;
  interval Ddel3 = x4 - x5 + x6;
  interval Ddel2 = x4 + x5 - x6;
  interval Pm5 =  (Ddel3 * x1 * u135 + del3 * u135 + del3 * x1 * du135) * 
    chain * (-four * x2 * u234 * two * y3);
  interval Pm6 = (Ddel2 * x1 * u126 + del2 * u126 + del2 * x1 * du126) *
    chain * (-four * x3 * u234 * two * y2);

  interval PrrC = two * Prhoy1 * m4 + rhoy1 * Pm4 + rhoy2 * Pm5 + rhoy3 * Pm6;
  interval P2tauNum = (PrrC) + (-Luf - half * Ldel) * rr;
  interval P2tau_uf = P2tauNum/ ( interMath::sqrt(del));

  show(Pm4,"Pm4"); show(Pm5,"Pm5"); show(Pm6,"Pm6"); show(PrrC,"Prrc");
  show(P2tauNum,"P2taunum"); show(P2tau_uf,"P2tau_uf");

  interval mdtau2uf = P2tau_uf;
  
  // set stored.
  y1b = y1; y2b = y2; y3b=y3; y4b=y4; y5b=y5; y6b=y6;
  mdtaub = mdtau; mdtau2ufb = mdtau2uf;


  report_values(y1,y2,y3,y4,y5,y6,mdtau,mdtau2uf);
  //return mdtau2uf;

};


interval wide::mdtau_y(const domain& x,const domain& z) {
  interval y[6];
  for (int i=0;i<6;i++) { y[i].lo = x.getValue(i); y[i].hi = z.getValue(i); }
  if (y1b==y[0] && y2b==y[1] && y3b==y[2] && y4b==y[3] && y5b==y[4] &&
      y6b== y[5]) { return mdtaub; }
  set_mdtau2uf(y[0],y[1],y[2],y[3],y[4],y[5]);
  if (y1b==y[0] && y2b==y[1] && y3b==y[2] && y4b==y[3] && y5b==y[4] &&
      y6b== y[5]) { return mdtaub; }
  else { error::message("stored mdtau failure"); }
};

interval wide::mdtau2uf_y(const domain& x,const domain& z) {
  interval y[6];
  for (int i=0;i<6;i++) { y[i].lo = x.getValue(i); y[i].hi = z.getValue(i); }
  if (y1b==y[0] && y2b==y[1] && y3b==y[2] && y4b==y[3] && y5b==y[4] &&
      y6b== y[5]) { return mdtau2ufb; }
  set_mdtau2uf(y[0],y[1],y[2],y[3],y[4],y[5]);
  if (y1b==y[0] && y2b==y[1] && y3b==y[2] && y4b==y[3] && y5b==y[4] &&
      y6b== y[5]) { return mdtau2ufb; }
  else { error::message("stored mdtau2uf failure"); }

  //  interval y[6];
  //for (int i=0;i<6;i++) { y[i].lo = x.getValue(i); y[i].hi = z.getValue(i); }
  //return  set_mdtau2uf(y[0],y[1],y[2],y[3],y[4],y[5]);
};

/***************************************************
 ** CODE for bcc_lattice.hl (not part of Flyspeck)
 ***************************************************/

const interval bcc_value = "5.31473969997195717";

interval selling_volume2_wide (interval p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
return  p01*p02*p03 + p01*p03*p12 + p02*p03*p12 +
  p01*p02*p13 + p02*p03*p13 + 
  p01*p12*p13 + p02*p12*p13 + p03*p12*p13 + 
  p01*p02*p23 + p01*p03*p23 + 
  p01*p12*p23 + p02*p12*p23 + p03*p12*p23 + 
    p01*p13*p23 + p02*p13*p23 + p03*p13*p23;
}


interval selling_surface_num_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * interMath::sqrt(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*interMath::sqrt(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
   return two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);;
}

interval selling_surface_nn_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  return selling_surface_num_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}

static interval o1 = "0.1";
interval sqrt01(interval t) {
  return  t* interMath::sqrt(o1) / (o1);
}

interval selling_surface_num2_013_approx_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * interMath::sqrt(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*sqrt01(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
    return two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);
}

interval selling_surface_nn2_013_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
 return    selling_surface_num2_013_approx_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}

interval selling_surface_num01_23_approx_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
 interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * sqrt01(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*interMath::sqrt(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
 return   two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);
}

interval selling_surface_nn01_23_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
return   selling_surface_num01_23_approx_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}


/*
Note: 5/19/2012.
This is code written in 3/2012.  The code for the root function
seems to be missing, and I don't know what happened to it.
I'll comment out this function for now.

interval selling_homog_wide(interval  y1,interval y2,interval y3,
			  interval y4, interval y5, interval y6) {
return 
   (selling_surface_num_wide (y1,y2,y3,y4,y5,y6)) -
  (bcc_value)*(root 6 (selling_volume2_wide (y1,y2,y3,y4,y5,y6) pow 5));
}
*/








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

  /* test mdtau */  {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  interval d = mdtau(y[0],y[1],y[2],y[3],y[4],y[5]);
  show(d,"mdtau");
  double v = -0.5994620477455596;
  if  (barelyLess(d.lo,v,eps) && barelyLess(v,d.hi,eps)) { } else { error::fatal("wide mdtau"); }
    }

  /* test mdtau */  {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  for (int i=0;i<6;i++) { y[i].hi += 0.01; }
  interval d = mdtau(y[0],y[1],y[2],y[3],y[4],y[5]);
  //cout << endl << d.lo << " " << d.hi << endl;
  // width is about 10, so about 1000x magnification.
    }


  /* test mdtau2uf */  {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  //interval d = set_mdtau2uf(y[0],y[1],y[2],y[3],y[4],y[5]);
  /* //no longer accurate.  These were calcs of mdtau2. Now we use mdtau2uf = mdtau2 * uf.
  show(d,"mdtau");
  double v = 0.2804657791758259;
  if  (barelyLess(d.lo,v,eps) && barelyLess(v,d.hi,eps)) { } else { error::fatal("wide mdtau2uf"); }
  */
  }

  /* test set_mdtau2uf */  {
  double eps = 1.0e-6;
  interval y[6] = {"2.1","2.2","2.3","3.4","2.5","2.6"};  
  for (int i=0;i<6;i++) { y[i].hi += 0.01; }
  //interval d = set_mdtau2uf(y[0],y[1],y[2],y[3],y[4],y[5]);
  //cout << endl << d.lo << " " << d.hi << endl;
  // width is about 1, so about 100x magnification.
  // It seems that the second derivative may be more numerically stable than the first!
    }




}

