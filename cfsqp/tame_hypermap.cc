/* ========================================================================== */
/* FLYSPECK - CFSQP                                              */
/*                                                                            */
/* Nonlinear Inequalities, C++ Nonrigorous Numerical Optimization   */
/* Chapter: Tame Hypermap                                                     */
/* Author: Thomas C. Hales                                                    */
/* Date: 2010-03-01                                                           */
/* ========================================================================== */

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// tame_hypermap.cc
// $ make tame_hypermap.o
// $ ./tame_hypermap.o

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

int trialcount = 300;
double eps = 1.0e-6;
double s8 = sqrt(8.0);

void assert_(int j,char* u) {
  if (!j) { 
    cout << "!!FAILURE: " << u << "\n";
  }
}

int value(double t1,double x1) {
  return (abs(t1 - x1) < 1.0e-8);
}

double test_function() {
  assert_(value(0.0,1.0),"entering test");
  assert_(value(interp(2.0,3.0,3.0,4.0,1.0),2.0),"interp");
  assert_(value(c1(),0.1754796560918218),"c1");
  assert_(value(ly(3.0),-0.9230769230769229),"ly");
  assert_(value(rho(3.0),1.3374608770996574),"rho");
  assert_(value(rhazim(2.05,2.1,2.15,2.2,2.25,2.3),1.2238197064544751),"rhazim");
  assert_(value(taum(2.05,2.1,2.15,2.2,2.25,2.3),0.23816478183286893),"taum");
}

double tauq(double y1,double y2,double y3,double y4,double y5,double y6,double y7,double y8,double y9) {
  return taum(y1,y2,y3,y4,y5,y6)+taum(y7,y2,y3,y4,y8,y9);
}

double deltay(double y1,double y2,double y3,double y4,double y5,double y6) {
  return delta_x(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6);
}

double deltaquad(int i,double y1,double y2,double y3,double y4,double y5,double y6,double y7,double y8,double y9) {
  return (i=0 ? deltay(y1,y2,y3,y4,y5,y6) : deltay(y7,y2,y3,y4,y8,y9));
}

//constraint: crossdiag > 2.52
void bigcross(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -crossdiag(y) +2.52;
};

//constraint: crossdiag > y[3]
void cross3(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -crossdiag(y) +y[3];
};

//constraint: y > 2.5
void testcon(int numargs,int whichFn,double* y, double* ret,void*) {
  switch(whichFn) {
  case 1: *ret = (-y[0] +2.5); break;
  default: *ret = -y[0] + 2.4; break;
  }
  
};

//constraint: crossdiag > 2.52, deltas positive.
void bigcrossdelta(int numargs,int whichFn,double* y, double* ret,void*) {
  switch(whichFn) {
  case 1: *ret = (-crossdiag(y) +2.52); break;
  case 2: *ret = -deltaquad(0,y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]); break;
  case 3: *ret = -deltaquad(1,y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]); break;
  }
};

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t3(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = azim(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.852;
	}
Minimizer m3() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t3;
	//.
	return M;
}
trialdata d3(m3(),"ID[5735387903] dihmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t3a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -azim(y[0],y[1],y[2],y[3],y[4],y[5]) + 1.893;
	}
Minimizer m3a() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t3a;
	//.
	return M;
}
trialdata d3a(m3a(),"ID[5490182221] dihmax");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5]) + 0.626*azim(y[0],y[1],y[2],y[3],y[4],y[5]) -0.77;
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t0;
	//.
	return M;
}
trialdata d0(m0(),"ID[3296257235] taum0: 0th taum-tri-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5]) -0.259*azim(y[0],y[1],y[2],y[3],y[4],y[5]) +0.32;
	}
Minimizer m1() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t1;
	//.
	return M;
}
trialdata d1(m1(),"ID[8519146937] taum1: 1st taum-tri-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5]) -0.507*azim(y[0],y[1],y[2],y[3],y[4],y[5]) +0.724;
	}
Minimizer m2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t2;
	//.
	return M;
}
trialdata d2(m2(),"ID[4667071578] taum2: 2nd taum-tri-ineq");


////////// QUAD CASES:
////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t4(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) +4.72*azim(y[0],y[1],y[2],y[3],y[4],y[5]) - 6.248;
	}
Minimizer m4() {
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 4.37,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,1,xmin,xmax);
	M.func = t4;
	M.cFunc = bigcross;
	return M;
}
trialdata d4(m4(),"ID[7043724150] tauq: 0 tauq-quad-ineq");


// this is minimized.  failure reported if min is negative.
void t4a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8])  - 0.256;
	}
Minimizer m4a() {
  double xmin[9]= {2,2,2, s8,2,2,2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 3,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,1,xmin,xmax);
	M.func = t4a;
	M.cFunc = cross3;
	return M;
}
trialdata d4a(m4a(),"ID[4930647408] m4a: tauq: 0 tauq-quad-ineq > 0.256");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t5(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) +0.972*azim(y[0],y[1],y[2],y[3],y[4],y[5]) - 1.707;
	}
Minimizer m5() {
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 4.37,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,1,xmin,xmax);
	M.func = t5;
	M.cFunc = bigcross;
	return M;
}
trialdata d5(m5(),"ID[6944699408] tauq: 1 tauq-quad-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t6(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) 
    +0.7573*azim(y[0],y[1],y[2],y[3],y[4],y[5])
   - 1.433;
	}
Minimizer m6() {
  double maxv = 3.5; // should really go to 2*2.52
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, maxv,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,3,xmin,xmax);
	M.func = t6;
	M.cFunc = bigcrossdelta;
	return M;
}
trialdata d6(m6(),"ID[4240815464] tauq: 2 tauq-quad-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t9(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) 
    -0.453*azim(y[0],y[1],y[2],y[3],y[4],y[5])
   + 0.777;
	}
Minimizer m9() {
  double maxv = 3.3; // should really go to 2*2.52
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, maxv,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,3,xmin,xmax);
	M.func = t9;
	M.cFunc = bigcrossdelta;
	return M;
}
trialdata d9(m9(),"ID[3862621143] tauq: 5 tauq-quad-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t8(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) 
    //0*azim(y[0],y[1],y[2],y[3],y[4],y[5])
    //(azim(y[2],y[0],y[1],y[5],y[3],y[4])+azim(y[2],y[6],y[1],y[8],y[3],y[7])) 
   - 0.206;
	}
Minimizer m8() {
  double maxv = 3.3; // should really go to 2*2.52
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, maxv ,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,3,xmin,xmax);
	M.func = t8;
	M.cFunc = bigcrossdelta;
	return M;
}
trialdata d8(m8(),"ID[5464178191] tauq: 4 tauq-quad-ineq");





int main() {
  test_function();
}
