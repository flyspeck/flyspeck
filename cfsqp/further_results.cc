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

double ac = - 0.5811692062216102;
double bc = 0.023248513304698123;

/* moved to numerical.cc
double interp(double x1,double y1,double x2,double y2, double x) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
*/

double Lfun(double r) {
  return interp(  1.0,1.0,    hmid,0.0,  r);
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
double saR(double a,double b,double c) {
  return 3.0*volR(a,b,c)/a;
}
double saRy(double y1,double y2,double y6,double c) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  return saR(a,b,c);
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

double surface(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = rady(y1,y2,y3,y4,y5,y6); 
  return saRy(y1,y2,y6,c) + saRy(y2,y1,y6,c)
    +saRy(y2,y3,y4,c) + saRy(y3,y2,y4,c)
    + saRy(y3,y1,y5,c) + saRy(y1,y3,y5,c);
}


double cell4(double y1,double y2,double y3,double y4,double y5,double y6) {
  double eps = 1.0e-15;  // avoid exact equality in numerical testing.
  return  eps + surface(y1,y2,y3,y4,y5,y6)/3.0
    + ac*sol_y(y1,y2,y3,y4,y5,y6) 
    + bc*rhazim4(y1,y2,y3,y4,y5,y6);
}

double rhazim3(double y1,double y2,double y6,double c) {
  return Lfun(y1/2)*dihRy(y1,y2,y6,c)
    +Lfun(y2/2)*dihRy(y2,y1,y6,c);
}

double cell3(double y1,double y2,double y6) {
  double c = 1.26; // pos: 1.267;
  return (saRy(y1,y2,y6,c)+saRy(y2,y1,y6,c))/3.0
    + ac*(solRy(y1,y2,y6,c)+solRy(y2,y1,y6,c))
    + bc*rhazim3(y1,y2,y6,c);
}



// surface area cone mod area.
double sa2moddih(double a,double c) {
  return (c*c-a*a)/2.0;  // Pi r^2.
}
double sol2moddih(double a,double c) {
  return (1.0 - a/c);  // 2Pi (1-cos theta)
}
double sa1modsol(double c) {
  return c*c; // 4 Pi r^2.
}

double saRya(double y1,double y2,double y6,double c1,double c2) {
  double a = y1/2.0;
  double b = radf(y1,y2,y6);
  double d = dihR(a,b,c2)-dihR(a,b,c1);
  double s = solR(a,b,c2) - solR(a,b,c1) - sol2moddih(a,c1)*d;
  return saR(a,b,c1) 
    + sa2moddih(a,c1)*d
    + sa1modsol(c1)*s;
}
double cell3a(double y1,double y2,double y6) {
  double c = 1.26; // pos: 1.267;
  double c2 = 1.3;
  return (saRya(y1,y2,y6,c,c2)+saRya(y2,y1,y6,c,c2))/3.0
    + ac*(solRy(y1,y2,y6,c2)+solRy(y2,y1,y6,c2))
    + bc*rhazim3(y1,y2,y6,c2);
}

double surfaceVc(double y1,double y2,double y3,double y4,double y5,double y6,double c) {
  double c2 = rady(y1,y2,y3,y4,y5,y6);
  return saRya(y1,y2,y6,c,c2) + saRya(y2,y1,y6,c,c2)
  +saRya(y2,y3,y4,c,c2) + saRya(y3,y2,y4,c,c2)
    +saRya(y3,y1,y5,c,c2) + saRya(y1,y3,y5,c,c2);
}

/*
double surface(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = rady(y1,y2,y3,y4,y5,y6); 
  return saRy(y1,y2,y6,c) + saRy(y2,y1,y6,c)
    +saRy(y2,y3,y4,c) + saRy(y3,y2,y4,c)
    + saRy(y3,y1,y5,c) + saRy(y1,y3,y5,c);
}
*/

double cell4Vc(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = 1.26;
  return  surfaceVc(y1,y2,y3,y4,y5,y6,c)/3.0
    + ac*sol_y(y1,y2,y3,y4,y5,y6) 
    + bc*rhazim4(y1,y2,y3,y4,y5,y6);
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


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell4(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t0;
	M.cFunc = smallradh;
	return M;
}
trialdata d0(m0(),"ID d0: Marchal (Strong Dodec) main 4-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell4Vc(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,2,xmin,xmax);
	M.func = t2;
	M.cFunc = midradh;
	return M;
}
trialdata d2(m2(),"ID d2: Marchal (Strong Dodec) main 4-cell inequality-trunc");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell3a(y[0],y[1],y[2]);
	}
Minimizer m1() {
  double xmin[3]= {2.03,2,2};
  double xmax[3]= {2.52,2.52,2.52};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradfh;
	return M;
}
trialdata d1(m1(),"ID d1: Marchal (Strong Dodec) main 3-cell inequality");


int main()
{

}
