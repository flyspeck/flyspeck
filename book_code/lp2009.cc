// nonlinear inequalities for linear programming relaxation.
// basic functions to be studied: azim, lnazim, sol (3), taum (3).

/* Thomas C. Hales
   file created June 17, 2009
   code to be used with cfsqp optimization.

 */

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// lp2009.cc
// $ make lp2009.o
// $ ./lp2009.o

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

int trialcount = 80;
double eps = 1.0e-6;

double interp(double x,double x1,double y1,double x2,double y2) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
double maxx(double a,double b) {
  return (a>b?a:b);
}
double minn(double a,double b) {
  return (a>b?b:a);
}


double ly(double y) {
  return interp(y,  2.0,1.0,    2.52,0.0);
}

double lnazim(double y1,double y2,double y3,double y4,double y5,double y6) {
  return ly(y1)*dih_y(y1,y2,y3,y4,y5,y6);
}

double azim(double y1,double y2,double y3,double y4,double y5,double y6) {
  return dih_y(y1,y2,y3,y4,y5,y6);
}

double sol(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sol_y(y1,y2,y3,y4,y5,y6);
}

double c1 = sol_y(2,2,2,2,2,2)/pi(); // delta0/Pi


double taum(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sol_y(y1,y2,y3,y4,y5,y6)*(1.0 + c1) - 
    c1*(lnazim(y1,y2,y3,y4,y5,y6)+lnazim(y2,y3,y1,y5,y6,y4)+lnazim(y3,y1,y2,y6,y4,y5));
}





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
	//M.cFunc = smallrad;
	return M;
}
trialdata d0(m0(),"ID taum0: 0th taum-tri-ineq");


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
	//M.cFunc = smallrad;
	return M;
}
trialdata d1(m1(),"ID taum1: 1st taum-tri-ineq");

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
	//M.cFunc = smallrad;
	return M;
}
trialdata d2(m2(),"ID taum2: 2nd taum-tri-ineq");

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
	//M.cFunc = smallrad;
	return M;
}
trialdata d3(m3(),"ID dihmin");




int main() {
}
