/* ========================================================================== */
/* FLYSPECK - CFSQP                                              */
/*                                                                            */
/* Nonlinear Inequalities, C++ Nonrigorous Numerical Optimization   */
/* Chapter: Further Results                                                     */
/* Author: Thomas C. Hales                                                    */
/* Date: 2010-03-01                                                           */
/* ========================================================================== */

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"

// strong dodecahedral conjecture and Fejes Toth's conj.
// Numerical testing of the local inequality on Dk-cells.

// further_results.cc
// $ make further_results.o
// $ ./further_results.o

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

int trialcount = 300;
double eps = 1.0e-6;
double s2 = sqrt(2.0);
double s8 = sqrt(8.0);
double hmid = 1.26; // 2.52 truncation

double aD = - 0.5811692062216102;
double bD = 0.023248513304698123;

/* moved to numerical.cc
double interp(double x1,double y1,double x2,double y2, double x) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
*/

double Lfun(double r) {
  return (r > 1.26? 0.0 : interp(  1.0,1.0,    hmid,0.0,  r));
}

double rhazimDR(double a,double b,double c) {
  return Lfun(a)*dihR(a,b,c);
}

double rhazim4(double y1,double y2,double y3,double y4,double y5,double y6) {
 return Lfun(y1/2)*dih_y(y1,y2,y3,y4,y5,y6)
   +Lfun(y2/2)*dih_y(y2,y3,y1,y5,y6,y4)
   +Lfun(y3/2)*dih_y(y3,y1,y2,y6,y4,y5);
}

// surface area calculations.
double surfR(double a,double b,double c) {
  return 3.0*volR(a,b,c)/a;
}
double surfRy(double y1,double y2,double y6,double c) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  return surfR(a,b,c);
}


double dihRy(double y1,double y2,double y6,double c) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  return dihR(a,b,c);
}
double solRy(double y1,double y2,double y6,double c) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  return solR(a,b,c);
}

//no truncation.
double surfD4(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = rady(y1,y2,y3,y4,y5,y6); 
  return surfRy(y1,y2,y6,c) + surfRy(y2,y1,y6,c)
    +surfRy(y2,y3,y4,c) + surfRy(y3,y2,y4,c)
    + surfRy(y3,y1,y5,c) + surfRy(y1,y3,y5,c);
}

//no truncation.
double cell4(double y1,double y2,double y3,double y4,double y5,double y6) {
  double eps = 1.0e-14;  // avoid exact equality in numerical testing.
  return  eps + surfD4(y1,y2,y3,y4,y5,y6)
    + 3.0*aD*sol_y(y1,y2,y3,y4,y5,y6) 
    + 3.0*bD*rhazim4(y1,y2,y3,y4,y5,y6);
}

double rhazim3(double y1,double y2,double y6,double c) {
  return Lfun(y1/2)*dihRy(y1,y2,y6,c)
    +Lfun(y2/2)*dihRy(y2,y1,y6,c);
}

//no truncation.
double cell3(double y1,double y2,double y6) {
  double c = sqrt(2.0);  //1.26; // pos: 1.267;
  return (surfRy(y1,y2,y6,c)+surfRy(y2,y1,y6,c))
    + 3.0*aD*(solRy(y1,y2,y6,c)+solRy(y2,y1,y6,c))
    + 3.0*bD*rhazim3(y1,y2,y6,c);
}




// surf cone mod dih.
double surfD2moddih(double a,double c) {
  return (c*c-a*a)/2.0;  // cone surface area = pi*b^2 = pi*(c^2-a^2).
}
double solD2moddih(double a,double c) {
  return (1.0 - a/c);  // 2Pi (1-cos theta)
}
// surf mod solid.
double surfD1modsol(double c) {
  return c*c; // 4 Pi c^2.
}

// surf of truncated D3-cell, within one Rogers cell.
double surfRya(double y1,double y2,double y6,double c1,double c2) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  double d = dihR(a,b,c2)-dihR(a,b,c1);
  double s = solR(a,b,c2) - solR(a,b,c1) - solD2moddih(a,c1)*d;
  return surfR(a,b,c1) 
    + surfD2moddih(a,c1)*d
    + surfD1modsol(c1)*s;
}
double cell3a(double y1,double y2,double y6) {
  double c = 1.26; // pos: 1.267;
  double c2 = 1.3;
  return (surfRya(y1,y2,y6,c,c2)+surfRya(y2,y1,y6,c,c2))/3.0
    + aD*(solRy(y1,y2,y6,c2)+solRy(y2,y1,y6,c2))
    + bD*rhazim3(y1,y2,y6,c2);
}

//no truncation.
double cellD2moddih(double y) {
  double c = sqrt(2.0); 
  return (surfD2moddih(y/2,c)
    + 3.0*aD*solD2moddih(y/2,c)
	  + 3.0*bD*Lfun(y/2));
}


double surfD4trunc(double y1,double y2,double y3,double y4,double y5,double y6,double c) {
  double c2 = rady(y1,y2,y3,y4,y5,y6);
  return surfRya(y1,y2,y6,c,c2) + surfRya(y2,y1,y6,c,c2)
  +surfRya(y2,y3,y4,c,c2) + surfRya(y3,y2,y4,c,c2)
    +surfRya(y3,y1,y5,c,c2) + surfRya(y1,y3,y5,c,c2);
}

/*
double surfD4(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = rady(y1,y2,y3,y4,y5,y6); 
  return surfRy(y1,y2,y6,c) + surfRy(y2,y1,y6,c)
    +surfRy(y2,y3,y4,c) + surfRy(y3,y2,y4,c)
    + surfRy(y3,y1,y5,c) + surfRy(y1,y3,y5,c);
}
*/

double cellD4trunc(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = 1.26;
  return  surfD4trunc(y1,y2,y3,y4,y5,y6,c)
    + 3.0*aD*sol_y(y1,y2,y3,y4,y5,y6) 
    + 3.0*bD*rhazim4(y1,y2,y3,y4,y5,y6);
}


//constraint rad < sqrt2:
void smallrad(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
}

//constraint rad < 1.26:
void smallradh(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - 1.26;
}

//constraint 12.6 < rad < 1.3:
void midradh(int numargs,int whichFn,double* y, double* ret,void*) {
  switch (whichFn) {
  case 1 : *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - 1.3; break;
  default: *ret = 1.26 - rady(y[0],y[1],y[2],y[3],y[4],y[5]); break;
  }
}

//constraint eta_y < 1.26:
void smallradfh(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - 1.26;
}

//constraint eta_y < sqrt2:
void smallradfh2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - s2;
}


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell4(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m0() {
  double yM = sqrt(8.0); // was 2.52.
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {yM,yM,yM,yM,yM,yM};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t0;
	M.cFunc = smallrad; // was smallradh.
	return M;
}
//trialdata d0(m0(),"ID d0: Marchal (Strong Dodec) main 4-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cellD4trunc(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,2,xmin,xmax);
	M.func = t2;
	M.cFunc = midradh;
	return M;
}
//trialdata d2(m2(),"ID d2: Marchal (Strong Dodec) main 4-cell inequality-trunc");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell3(y[0],y[1],y[2]);
	}
Minimizer m1() {
  double yM = sqrt(8.0);
  double xmin[3]= {2,2,2};
  double xmax[3]= {yM,yM,yM}; //{2.52,2.52,2.52};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradfh2; // smallradfh;
	return M;
}
trialdata d1(m1(),"ID d1: Marchal (Strong Dodec) main 3-cell inequality");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t3(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cellD2moddih(y[0]);
	}
Minimizer m3() {
  double yM = sqrt(8.0);
  double xmin[1]= {2};
  double xmax[1]= {yM};
	Minimizer M(trialcount,1,0,xmin,xmax);
	M.func = t3;
	return M;
}
trialdata d3(m3(),"ID d3: Marchal (Strong Dodec) main 2-cell inequality");



// The 0-cell inequality is just
// surfD1modsol  + 3.0*aD > 0.

int main()
{

}
