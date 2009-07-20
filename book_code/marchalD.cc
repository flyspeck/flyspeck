#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"

// Marhal adapted to dodecahedral conjecture.

// marchalD.cc
// $ make marchalD.o
// $ ./marchalD.o

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


double interp(double x,double x1,double y1,double x2,double y2) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}

double Lfun(double r) {
  return interp(r,  1.0,1.0,    hmid,0.0);
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

double surface_area(double y1,double y2,double y3,double y4,double y5,double y6) {
  double c = rady(y1,y2,y3,y4,y5,y6); 
  return saRy(y1,y2,y6,c) + saRy(y2,y1,y6,c)
    +saRy(y2,y3,y4,c) + saRy(y3,y2,y4,c)
    + saRy(y3,y1,y5,c) + saRy(y1,y3,y5,c);
}


double cell4(double y1,double y2,double y3,double y4,double y5,double y6) {
  return  surface_area(y1,y2,y3,y4,y5,y6)/3.0
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



//constraint rad < sqrt2:
void smallrad(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
};
//constraint rad < 1.26:
void smallradh(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - 1.26;
};
//constraint eta_y < s2:
void smallradf(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - (s2);
};
//constraint eta_y < 1.26:
void smallradfh(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - 1.26;
};


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
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = cell3(y[0],y[1],y[2]);
	}
Minimizer m1() {
  double xmin[3]= {2,2,2};
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
