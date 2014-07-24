/* ========================================================================== */
/* FLYSPECK - CFSQP                                              */
/*                                                                            */
/* Nonlinear Inequalities, C++ Nonrigorous Numerical Optimization   */
/* Chapter: Local Fan                                                     */
/* Author: Thomas C. Hales                                                    */
/* Date: 2010-03-01                                                           */
/* ========================================================================== */

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// local_fan.cc
// $ make local_fan.o
// $ ./local_fan.o

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

double Power(double a,int b) {
  return pow(a,(float) b);
}

int trialcount = 300;
double eps = 1.0e-6;
double s2 = sqrt(2.0);
double s8 = sqrt(8.0);
double h0 = 1.26;
double sol0 = 0.5512855984325309;


////////// NEW INEQ
double taum_d1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-8;
  return (taum(y1+h,y2,y3,y4,y5,y6)-taum(y1,y2,y3,y4,y5,y6))/h;
}
double taum_d2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-8;
  return (taum(y1+h,y2,y3,y4,y5,y6)-2*taum(y1,y2,y3,y4,y5,y6) + taum(y1-h,y2,y3,y4,y5,y6))/(h*h);
}
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum_d1(y[0],y[1],y[2],y[3],y[4],y[5]) ;
  *ret = r*r ;
	}
Minimizer m1() {
   double xmin[6]= {2,2,2,2.52,2.52,2};
   double xmax[6]= {2.52,2.52,2.52,3.0,2.52,2.52};   
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t1;
	return M;
}
//trialdata d1(m1(),"ID[DWXPIHA] ID[] d1: extreme-- FALSE!!. Gives C/E to y1-deformaton");

////////// NEW INEQ






////////// NEW INEQ
// d0
double gt0(double a,double b,double c,double e1,double e2,double e3) {
  return( dih_y(2,2,2,a,b,c)*e1
     + dih2_y(2,2,2,a,b,c)*e2
	  + dih3_y(2,2,2,a,b,c)*e3);
}
double gt1(double a,double b,double c,double e1,double e2,double e3) {
  return( (-4*(Power(a,4)*e1 + 8*(Power(b,2) - Power(c,2))*(e2 - e3) - 
     Power(a,2)*(16*e1 + (-8 + Power(b,2))*e2 + 
		 (-8 + Power(c,2))*e3)))/(a*(16-a*a)) );
}
double gt2(double a,double b,double c,double e1,double e2,double e3) {
  double num = 8*(2*Power(a,10)*e1 - 256*Power(Power(b,2) - Power(c,2),3)*
      (e2 - e3) - Power(a,6)*
      (2*(-256 + Power(b,4) - 2*Power(b,2)*Power(c,2) + 
           Power(c,4))*e1 + 
        (Power(b,4)*(-8 + Power(c,2)) - 
           16*Power(b,2)*(3 + Power(c,2)) + 
           16*(16 + 9*Power(c,2)))*e2 + 
        (Power(b,2)*(144 - 16*Power(c,2) + Power(c,4)) - 
           8*(-32 + 6*Power(c,2) + Power(c,4)))*e3) + 
     Power(a,8)*(-64*e1 - 
        6*((-8 + Power(b,2))*e2 + (-8 + Power(c,2))*e3)) - 
     2*Power(a,4)*(Power(b,2) - Power(c,2))*
      (Power(b,4)*e2 + 8*Power(c,2)*(4*e1 + 9*e2 - 7*e3) + 
        384*(e2 - e3) - Power(c,4)*e3 + 
        Power(b,2)*(-32*e1 + (56 - 9*Power(c,2))*e2 + 
           9*(-8 + Power(c,2))*e3)) + 
     16*Power(a,2)*(Power(b,2) - Power(c,2))*
      (Power(b,4)*(e2 - 3*e3) - 
        4*Power(b,2)*(8*e1 + (-20 + 3*Power(c,2))*e2 - 
           3*(-4 + Power(c,2))*e3) + 
        Power(c,2)*(32*e1 + 3*(16 + Power(c,2))*e2 - 
           (80 + Power(c,2))*e3))) ;
  double den = Power(a* (16 - a*a),2);
  return( num/den);
}
//constraint delta>0, deriv2>0.
void deltaposlast(int numargs,int whichFn,double* y, double* ret,void*) {
  double a = y[3]; double b = y[4]; double c= y[5];
  double e1 = y[0]; double e2 = y[1]; double e3 = y[2];
  double deriv = gt1(a,b,c,e1,e2,e3);
  double deriv2 = gt2(a,b,c,e1,e2,e3);
  double r= -deriv2;
  if (whichFn==1) { r =  -delta_y(2,2,2,y[3],y[4],y[5]); }
  *ret = r;
}
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  double a = y[3]; double b = y[4]; double c= y[5];
  double e1 = y[0]; double e2 = y[1]; double e3 = y[2];
  double deriv= gt1(a,b,c,e1,e2,e3);
  double deriv2 = gt2(a,b,c,e1,e2,e3);
  double r= deriv*deriv - 0.01*deriv2;  
  // 0.00001 -> 0.00129
  // 0.0001 -> 0.01289
  // 0.001 -> 0.1225
  // 0.01 -> 0.89 // use this
  // 0.1 -> -655.814.
  *ret = r ;
	}
Minimizer m0() {
  double t = 1.0 + sol0/pi();
  double xmin[6]= {1,1,1,2/h0,2/h0,2/h0};
  double xmax[6]= {t,t,t,4,4,4};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t0;
	return M;
}
trialdata d0(m0(),"ID[2065952723] d0: Lexell variant.");

double cc(double y1,double y2,double y,double a,double b) {
  // Delta_y(y1,y2,y,a,b,cc)=0.
  double x1 = y1*y1;
  double x2 = y2*y2;
  double x = y*y;
  double aa = a*a;
  double bb = b*b;
  double ub = U(bb,x,x1);
  double ua = U(aa,x,x2);
  double dd = -aa*bb + aa*x + bb*x - x*x + aa*x1 + x*x1 + bb*x2 + x*x2 - x1*x2;
  double c = (1.0/(2.0*x))*(dd + sqrt(ua*ub));
  return sqrt(c);
}
double taum_e0(double y1,double y2,double y3,double y4,double y5,double y) {
  double a = 2.0;
  double b = 2.0;
  double c = cc(y1,y2,y,a,b);
  return taum(y1,y2,y3,y4,y5,c) + pi()*rho(y);
}
double taum_e1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-8;
  return (taum_e0(y1,y2,y3,y4,y5,y6+h)-taum_e0(y1,y2,y3,y4,y5,y6))/h;
}
double taum_e2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-4;
  return (taum_e0(y1,y2,y3,y4,y5,y6+h)-2*taum_e0(y1,y2,y3,y4,y5,y6) + taum_e0(y1,y2,y3,y4,y5,y6-h))/(h*h);
}
void c2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -taum_e2(y[0],y[1],y[2],y[3],y[4],y[5]);
}
// this is minimized.  failure reported if min is negative.
void t2(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum_e1(y[0],y[1],y[2],y[3],y[4],y[5]) ;
  double r2 =  taum_e2(y[0],y[1],y[2],y[3],y[4],y[5]) ;
  *ret = r*r ;
  // 0.01  gives neg
  // 
	}
Minimizer m2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,4.0,2.52,2.52};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t2;
        M.cFunc = c2;
	return M;
}
//trialdata d2(m2(),"experiment ID[] ID[] d2:  gives C/E to a particular deformation. Adjusting the height at a flat vertex.");



////////// NEW INEQ
double taum4_d1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-8;
  return (taum(y1,y2,y3,y4+h,y5,y6)-taum(y1,y2,y3,y4,y5,y6))/h;
}
double taum4_d2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-4;
  return (taum(y1,y2,y3,y4+h,y5,y6)-2*taum(y1,y2,y3,y4,y5,y6) + taum(y1,y2,y3,y4-h,y5,y6))/(h*h);
}
void t11(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum4_d1(y[0],y[1],y[2],y[3],y[4],y[5])+taum4_d1(y[6],y[1],y[2],y[3],y[7],y[8]);
  double s= taum4_d2(y[0],y[1],y[2],y[3],y[4],y[5])+taum4_d2(y[6],y[1],y[2],y[3],y[7],y[8]);
  *ret = r*r - 0.01*s ;
	}
void c11(int numargs,int whichFn,double* y, double* ret,void*) {
  double s= taum4_d2(y[0],y[1],y[2],y[3],y[4],y[5])+taum4_d2(y[6],y[1],y[2],y[3],y[7],y[8]);
  switch(whichFn) {
  case 1: *ret = y[3]-crossdiag(y); 
    break;
  case 2: *ret = dih3_y(y[0],y[1],y[2],y[3],y[4],y[5]) + dih_y(y[2],y[1],y[6],y[8],y[7],y[3]) - pi(); 
    break;
  case 3: *ret = -  delta_y(y[0],y[1],y[2],y[3],y[4],y[5]); 
    break;
  case 4: *ret = -  delta_y(y[2],y[1],y[6],y[8],y[7],y[3]); 
    break;
  case 5: *ret = -s;
    break;
  default: *ret = -s;
    break;
  }
}
Minimizer m11() {
  double xmin[9]= {2,2,2,                     2.52,2,2.52,                   2,2,2};
  double xmax[9]= {2.52,2.52,2.52,     3.9,2.52,3.9,                  2.52,2.52,2.52};//ok to 4.0
	Minimizer M(trialcount,9,4,xmin,xmax);
	M.func = t11;
	M.cFunc = c11;
	return M;
}
trialdata d11(m11(),"m11: ID[2986512815] cc:qua: two simplices common diagonal, no local minimum, (not full domain)");
/*
  Minimizer M(trialcount*300,9,4,xmin,xmax);
constrained min: 0.0049666912319060166
variables: {2.02287626223235639, 2.52000000000000002, 2.5199999999994307, 2.86885817213602401, 2.00649572338011328, 2.58689726914902973, 2.00000000000637002, 2.00000000000699529, 2.00000000000699529}
 */



////////// NEW INEQ
void t12(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5]) + 1.0e-8;
  *ret = r;
	}
Minimizer m12() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2.52,2.52,2.52,2,2,2};
  Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t12;
	return M;
}
trialdata d12(m12(),"d12: ID[6147439478] Main Inequality Triangles [3,0]");

////////// NEW INEQ
void t13(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])-0.103;
  *ret = r;
	}
Minimizer m13() {
  double xmin[6]= {2,2,2,2,2,2.52};
  double xmax[6]= {2.52,2.52,2.52,2,2,2.52};
  Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t13;
	return M;
}
trialdata d13(m13(),"d13: ID[4760233334] Main Inequality Triangles [2,1]");


////////// NEW INEQ
void t14(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])-0.2759;
   *ret = r;
	}
Minimizer m14() {
  double xmin[6]= {2,2,2,2,2.52,2.52};
  double xmax[6]= {2.52,2.52,2.52,2,2.52,2.52};
  Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t14;
	return M;
}
trialdata d14(m14(),"d14: ID[4663664691] Main Inequality Triangles [1,2]");


////////// NEW INEQ
void t15(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])-0.4488;
    *ret = r;
	}
Minimizer m15() {
  double xmin[6]= {2,2,2,2.52,2.52,2.52};
  double xmax[6]= {2.52,2.52,2.52,2.52,2.52,2.52};
  Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t15;
	return M;
}
trialdata d15(m15(),"d15: ID[9098044151] Main Inequality Triangles [0,3]");

////////// NEW INEQ
void t16(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.206;
    *ret = r;
	}
Minimizer m16() {
  double xmin[9]= {2,2,2,2.52,2,2,2,2,2};
  double xmax[9]= {2.52,2.52,2.52,sqrt(8.0),2,2,2.52,2,2};
  Minimizer M(trialcount,9,0,xmin,xmax);
	M.func = t16;
	return M;
}
trialdata d16(m16(),"d16: ID[] Main Inequality Quad [4,0]");

////////// NEW INEQ
void t17(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.3789;
    *ret = r;
	}
Minimizer m17() {
  double xmin[9]= {2,2,2,2.52,2.52,2,2,2,2};
  double xmax[9]= {2.52,2.52,2.52,3.1,2.52,2,2.52,2,2}; // shorter diag.
  Minimizer M(trialcount,9,0,xmin,xmax);
	M.func = t17;
	return M;
}
trialdata d17(m17(),"d17: ID[] Main Inequality Quad [3,1]");

////////// NEW INEQ
void t18(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.5518;
    *ret = r;
	}
Minimizer m18() {
  double xmin[9]= {2,2,2,2.52,2.52,2,2,2.52,2};
  double xmax[9]= {2.52,2.52,2.52,3.22,2.52,2,2.52,2.52,2}; // shorter diag.
  Minimizer M(trialcount,9,0,xmin,xmax);
	M.func = t18;
	return M;
}
trialdata d18(m18(),"d18: ID[] Main Inequality Quad [2,2]a");


////////// NEW INEQ
void t19(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.5518;
    *ret = r;
	}
Minimizer m19() {
  double xmin[9]= {2,2,2,2.52,2.52,2.52,2,2,2};
  double xmax[9]= {2.52,2.52,2.52,3.2,2.52,2.52,2.52,2,2}; // shorter diag.
  Minimizer M(trialcount,9,0,xmin,xmax);
	M.func = t19;
	return M;
}
trialdata d19(m19(),"d19: ID[] Main Inequality Quad [2,2]b");


////////// NEW INEQ
void t20(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.5518;
    *ret = r;
	}
Minimizer m20() {
  double xmin[9]= {2,2,2,2.52,2.52,2,2,2,2.52};
  double xmax[9]= {2.52,2.52,2.52,3.2,2.52,2,2.52,2,2.52}; // shorter diag.
  Minimizer M(trialcount,9,0,xmin,xmax);
	M.func = t20;
	return M;
}
trialdata d20(m20(),"d20: ID[] Main Inequality Quad [2,2]c");


////////// NEW INEQ
void t21(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])+taum(y[6],y[1],y[2],y[3],y[7],y[8])-0.5518;
    *ret = r;
	}
void c21(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= -crossdiag(y) + y[3];
    *ret = r;
	}
Minimizer m21() {
  double xmin[9]= {2,2,2,2.52,2.52,2,2,2,2.52};
  double xmax[9]= {2.52,2.52,2.52,3.57,2.52,2.52,2.52,2.52,2.52}; // shorter diag.
  Minimizer M(trialcount,9,1,xmin,xmax);
	M.func = t21;
	M.cFunc = c21;
	return M;
}
trialdata d21(m21(),"d21: ID[] Main Inequality Quad [2,2]d");

////////// NEW INEQ
void t22(int numargs,int whichFn,double* y, double* ret,void*) {
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])
    +taum(y[0],y[2],y[6],y[7],y[8],y[4])
    +taum(y[0],y[6],y[9],y[10],y[11],y[8])
    -0.4819;
    *ret = r;
	}
void c22(int numargs,int whichFn,double* y, double* ret,void*) {
  double r = 0;
  switch(whichFn) {
  case 1: r = dih_y(y[0],y[1],y[2],y[3],y[4],y[5])
    +dih_y(y[0],y[2],y[6],y[7],y[8],y[4])
      +dih_y(y[0],y[6],y[9],y[10],y[11],y[8]) - dih_y(y[0],y[1],y[9],2.52,y[11],y[5]);
    break;
  case 2:
    r = dih_y(y[2],y[0],y[1],y[5],y[3],y[4]) + dih_y(y[2],y[0],y[6],y[8],y[7],y[4])
      - dih_y(y[2],y[1],y[6],2.52,y[7],y[3]);
    break;
  case 3:
    r = dih_y(y[6],y[2],y[0],y[4],y[8],y[7])+dih_y(y[6],y[0],y[9],y[11],y[10],y[8])
      - dih_y(y[6],y[2],y[9],2.52,y[10],y[7]);
    break;
  case 4:
    r=delta_y(y[0],y[1],y[2],y[3],y[4],y[5]);
    break;
  default:
    r=delta_y(y[0],y[6],y[9],y[10],y[11],y[8]);
    break;
  }
    *ret = -r;
	}
Minimizer m22() {
  double xmin[12]= {2,2,2, 2,2.52,2, 2,2,2.52,   2,2,2};
  double xmax[12]= {2.52,2.52,2.52,  2,3,2,  2.52,2,3,   2.52,2,2};
  Minimizer M(trialcount,12,5,xmin,xmax);
	M.func = t22;
	M.cFunc = c22;
	return M;
}
trialdata d22(m22(),"d22: ID[] Main Inequality Pent [5,0] (not full domain)");

////////// NEW INEQ
void t23(int numargs,int whichFn,double* y, double* ret,void*) {
  // these label vertices of triangulation of a pentagon.
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])
    +taum(y[0],y[2],y[6],y[7],y[8],y[4])
    +taum(y[0],y[6],y[9],y[10],y[11],y[8])
    -0.6548;
    *ret = r;
	}
void c23(int numargs,int whichFn,double* y, double* ret,void*) {
  double r = 0;
  switch(whichFn) {
  case 1: r = dih_y(y[0],y[1],y[2],y[3],y[4],y[5])
    +dih_y(y[0],y[2],y[6],y[7],y[8],y[4])
      +dih_y(y[0],y[6],y[9],y[10],y[11],y[8]) - dih_y(y[0],y[1],y[9],2.52,y[11],y[5]);
    break;
  case 2:
    r = dih_y(y[2],y[0],y[1],y[5],y[3],y[4]) + dih_y(y[2],y[0],y[6],y[8],y[7],y[4])
      - dih_y(y[2],y[1],y[6],2.52,y[7],y[3]);
    break;
  case 3:
    r = dih_y(y[6],y[2],y[0],y[4],y[8],y[7])+dih_y(y[6],y[0],y[9],y[11],y[10],y[8])
      - dih_y(y[6],y[2],y[9],2.52,y[10],y[7]);
    break;
  case 4:
    r=delta_y(y[0],y[1],y[2],y[3],y[4],y[5]);
    break;
  default:
    r=delta_y(y[0],y[6],y[9],y[10],y[11],y[8]);
    break;
  }
    *ret = -r;
	}
Minimizer m23() {
  double xmin[12]= {2,2,2, 2,2.52,2, 2,2.52,2.52,   2,2,2};
  double xmax[12]= {2.52,2.52,2.52,  2.52,3,2.52,  2.52,2.52,3,   2.52,2.52,2.52};
  Minimizer M(trialcount,12,5,xmin,xmax);
	M.func = t23;
	M.cFunc = c23;
	return M;
}
trialdata d23(m23(),"d23: ID[] Main Inequality Pent [4,1] (not full domain)");

////////// NEW INEQ
void t24(int numargs,int whichFn,double* y, double* ret,void*) {
  // these label vertices of triangulation of a hexagon.
  double r= taum(y[0],y[1],y[2],y[3],y[4],y[5])
    +taum(y[6],y[1],y[2],y[3],y[7],y[8])
    +taum(y[9],y[0],y[2],y[4],y[11],y[10])
    +taum(y[12],y[0],y[1],y[5],y[13],y[14])
    -0.7578;
    *ret = r;
	}
void c24(int numargs,int whichFn,double* y, double* ret,void*) {
  double r = 0;
  switch(whichFn) {
  case 1: r = dih_y(y[0],y[1],y[2],y[3],y[4],y[5])
      +dih_y(y[0],y[12],y[1],y[13],y[5],y[14])
      +dih_y(y[0],y[9],y[2],y[11],y[4],y[10])
      - dih_y(y[0],y[9],y[12],2.52,y[14],y[10]);
    break;
  case 2:
    r = dih_y(y[1],y[0],y[2],y[4],y[3],y[5])
      +dih_y(y[1],y[0],y[12],y[14],y[13],y[5])
      +dih_y(y[1],y[2],y[6],y[7],y[8],y[3])
      - dih_y(y[1],y[12],y[6],2.52,y[8],y[13]);
    break;
  case 3:
    r = dih_y(y[2],y[1],y[0],y[5],y[4],y[3])
      +dih_y(y[2],y[6],y[1],y[8],y[3],y[7])
      +dih_y(y[2],y[0],y[9],y[10],y[11],y[4])
      - dih_y(y[2],y[9],y[6],2.52,y[7],y[11]);
    break;
  case 4:
    r=delta_y(y[6],y[1],y[2],y[3],y[7],y[8]);
    break;
  case 5:
    r=delta_y(y[9],y[0],y[2],y[4],y[11],y[10]);
    break;
  case 6:
    r=delta_y(y[12],y[0],y[1],y[5],y[13],y[14]);
    break;
  case 7:
    r = crossdiag(y) - y[3];
    break;
  case 8:
    r = y[3]- y[4];
    break;
  case 9:
    r = delta_y(y[0],y[1],y[2],y[3],y[4],y[5]);
    break;
  default: r = y[4]-y[5];
  }
    *ret = -r;
	}
Minimizer m24() {
  double xmin[15]= {2,2,2, 2.52,2.52,2.52, 2,2,2,   2,2,2, 2,2,2};
  double xmax[15]= {2.52,2.52,2.52,  3.8,3.8,3.8,  2.52,2.52,2.52,   2.52,2.52,2.52, 2.52,2.52,2.52};
  Minimizer M(trialcount,15,10,xmin,xmax);
	M.func = t24;
	M.cFunc = c24;
	return M;
}
trialdata d24(m24(),"d24: ID[] Main Inequality Hex [6,0] (not full domain)");



int main()
{
  //  cout << dih_y (2.01,2.02,2.03,2.04,2.05,2.06);;
double y[9] = {2.01757248069328288, 2.00385313357932526, 2.05784751769748242, 
2.66743320268093287, 2.02045376048810033, 3.7968261622461, 
	       2.08361068848451136, 2.17839994782590241, 2.01394807769320305};
  cout <<  dih3_y(y[0],y[1],y[2],y[3],y[4],y[5]) + dih_y(y[2],y[1],y[6],y[8],y[7],y[3]) - pi(); 
}
