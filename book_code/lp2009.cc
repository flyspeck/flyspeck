// nonlinear inequalities for linear programming relaxation.
// basic functions to be studied: azim, rhazim, sol (3), taum (3).

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

int trialcount = 300;
double eps = 1.0e-6;
double s8 = sqrt(8.0);

double interp(double x,double x1,double y1,double x2,double y2) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
double maxx(double a,double b) {
  return (a>b?a:b);
}
double minn(double a,double b) {
  return (a>b?b:a);
}

double c1 = sol_y(2,2,2,2,2,2)/pi(); // delta0/Pi

double ly(double y) {
  return interp(y,  2.0,1.0,    2.52,0.0);
}
double rho(double y) {
  return (1+c1) - c1*ly(y);
}

double rhazim(double y1,double y2,double y3,double y4,double y5,double y6) {
  return rho(y1)*dih_y(y1,y2,y3,y4,y5,y6);
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




double taum(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sol_y(y1,y2,y3,y4,y5,y6)*(1.0 + c1) - 
    c1*(lnazim(y1,y2,y3,y4,y5,y6)+lnazim(y2,y3,y1,y5,y6,y4)+lnazim(y3,y1,y2,y6,y4,y5));
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
	//M.cFunc = smallrad;
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
	//M.cFunc = smallrad;
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
	//M.cFunc = smallrad;
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
	//M.cFunc = smallrad;
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
	//M.cFunc = smallrad;
	return M;
}
trialdata d2(m2(),"ID[4667071578] taum2: 2nd taum-tri-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t10(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5]) + 0.001
    - 0.18 * (y[0]+y[1]+y[2] - 6) - 0.125* (y[3]+y[4]+y[5]-6) ;
	}
Minimizer m10() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t10;
	//M.cFunc = smallrad;
	return M;
}
trialdata d10(m10(),"ID[1395142356] taum:  taum-y-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t11(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = sol_y(y[0],y[1],y[2],y[3],y[4],y[5]) -
   0.55125
    - 0.196 *(y[3]+y[4]+y[5]-6) + 0.38*(y[0]+y[1]+y[2]-6);
	}
Minimizer m11() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t11;
	//M.cFunc = smallrad;
	return M;
}
//compare J_544014470 from 1998
trialdata d11(m11(),"ID[7394240696]:  sol-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t13(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -sol_y(y[0],y[1],y[2],y[3],y[4],y[5]) + 0.5513
    + 0.3232 * (y[3]+y[4]+y[5]-6) 
    - 0.151*(y[0]+y[1]+y[2]-6);
	}
Minimizer m13() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t13;
	//M.cFunc = smallrad;
	return M;
}
//compare J_38243071
trialdata d13(m13(),"ID[7726998381] taum:  sol-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t12(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) -
   1.2308
    +0.3639 *(y[1]+y[2]+y[4]+y[5]-8) - 0.235*(y[0]-2) - 0.685*(y[3]-2);
	}
Minimizer m12() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t12;
	//M.cFunc = smallrad;
	return M;
}
//compare J_568731327 from 1998
trialdata d12(m12(),"model(azminA):ID[4047599236] taum:  dih-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t14(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -azim(y[0],y[1],y[2],y[3],y[4],y[5]) + 1.231
    - 0.152 * (y[1]+y[2]+y[4]+y[5]-8) 
    + 0.5*(y[0]-2)
    + 0.773*(y[3]-2);
	}
Minimizer m14() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t14;
	//M.cFunc = smallrad;
	return M;
}
//compare J_507227930
trialdata d14(m14(),"ID[3526497018] taum:  dih-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t15(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rhazim(y[0],y[1],y[2],y[3],y[4],y[5]) -
   1.2308
    +0.3639 *(y[1]+y[2]+y[4]+y[5]-8) - 0.60*(y[0]-2) - 0.685*(y[3]-2); 
	}
Minimizer m15() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t15;
	//M.cFunc = smallrad;
	return M;
}
//compare J_507227930
trialdata d15(m15(),"ID[5957966880] taum:  rhazim-ineq");



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
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 3.5,2.52,2.52, 2.52,2.52,2.52};
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
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 3.3,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,3,xmin,xmax);
	M.func = t9;
	M.cFunc = bigcrossdelta;
	return M;
}
trialdata d9(m9(),"ID[3862621143] tauq: 5 tauq-quad-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t7(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = y[0];
	}
Minimizer m7() {
  double xmin[1]= {2};
  double xmax[1]= {3};
	Minimizer M(trialcount,1,1,xmin,xmax);
	M.func = t7;
	M.cFunc = testcon;
	return M;
}
//trialdata d7(m7(),"test of constraints");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t8(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tauq(y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8]) 
    //0*azim(y[0],y[1],y[2],y[3],y[4],y[5])
    //(azim(y[2],y[0],y[1],y[5],y[3],y[4])+azim(y[2],y[6],y[1],y[8],y[3],y[7])) 
   - 0.206;
	}
Minimizer m8() {
  double xmin[9]= {2,2,2, 2.52,2,2, 2,2,2};
  double xmax[9]= {2.52,2.52,2.52, 3.3,2.52,2.52, 2.52,2.52,2.52};
	Minimizer M(trialcount,9,3,xmin,xmax);
	M.func = t8;
	M.cFunc = bigcrossdelta;
	return M;
}
trialdata d8(m8(),"ID[5464178191] tauq: 4 tauq-quad-ineq");











////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t16(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) -
   1.629
    +0.402 *(y[1]+y[2]+y[4]+y[5]-8) - 0.315*(y[0]-2) ;
	}
Minimizer m16() {
  double xmin[6]= {2,2,2,2.52,2,2};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t16;
	//M.cFunc = smallrad;
	return M;
}
//compare J_568731327 from 1998
trialdata d16(m16(),"ID[3020140039]:  dih-quad-min-ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t17(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) -
   1.91
    +0.458 *(y[1]+y[2]+y[4]+y[5]-8) - 0.342*(y[0]-2) ; 
	}
Minimizer m17() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2,2,2,s8,2,2};
  double xmax[6]= {2.52,2.52,2.52,s8,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t17;
	//M.cFunc = smallrad;
	return M;
}
//compare J_568731327 from 1998
trialdata d17(m17(),"ID[9414951439]:  dih-super8-min-ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t30(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5])  -0.1
    - 0.265*(y[4]+y[5]-4) -0.06 *(y[3]-2.52) -0.16*(y[0]-2) - 0.115*(y[1]+y[2]-4);
	}
Minimizer m30() {
  double xmin[6]= {2,2,2,2.52,2,2};
  double xmax[6]= {2.52,2.52,2.52,s8,2.52,2.52};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t30;
	return M;
}
trialdata d30(m30(),"ID[8248508703] taum: flat quarter");


int main() {

}
