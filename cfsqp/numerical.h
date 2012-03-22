//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifndef ineq_c
#define ineq_c

// These routines use ordinary floating point arithmetic without any
// reference to IEEE-754 standards, rounding modes, interval methods, etc.
// They cannot be used in the rigorous verification of inequalities.
// They can be used to propose and test inequalities that are to be
// proved later by rigorous means.

/* names conforming to definitions_kepler.ml:
pi,delta_x,sol_y,dih_y
 */

// math.
double pi();
double adodec();
double bdodec();
//double pt();
double max(double a,double b);
double real_max(double a,double b);
double min(double a,double b);
double real_pow(double a,double b);
double root(double n,double x);
double atn2(double x,double y);  // = atan(y/x) in first quadrant.
double matan(double); // atan(sqrt(x))/(sqrt(x)), and analytic continuation
double asn(double x);

double sqp(double x);  // upper bound on sqrt that is analytic near 0.
double sqn(double x);  // lower bound on sqrt that is analytic near 0.

// simplex:
double delta_x(double x1,double x2,double x3,double x4,double x5,double x6);
double delta_y(double y1,double y2,double y3,double y4,double y5,double y6);
double sol_y(double y1,double y2,double y3,double y4,double y5,double y6);
double dih_y(double y1,double y2,double y3,double y4,
                        double y5, double y6);
double dih2_y(double y1,double y2,double y3,double y4,
                        double y5, double y6);
double dih3_y(double y1,double y2,double y3,double y4,
                        double y5, double y6);

// deprecated: an upper bound on dih_y, valid when d4 <0.
//double upper_dih_y_large(double y1,double y2,double y3,double y4,double y5,
//			 double y6);

// circumradius: 
double eta2(double x1,double x2,double x3);
double radf(double y1,double y2,double y3);
double chi(double x1,double x2,double x3,double x4,double x5,double x6);
double circum2(double x1,double x2,double x3,double x4,double x5,double x6);
double rady(double y1,double y2,double y3,double y4,double y5,double y6);
double arc(double y1,double y2,double y6);
double U(double a,double b,double c);


// scoring:


// rogers:/abc parameters.
double dihR(double a,double b,double c);
double solR(double a,double b,double c);
//double volR(double a,double b,double c);


// misc:
double mabs(double a);
double safesqrt(double x);

// full quad cluster:
// we use mod three numbering:
//  	indices on back simplex are standard order mod 3.
//
//y[0],y[1],y[2],y[3],y[4],y[5] = 1st simplex. y[3]=diag.
//y[6],y[1],y[2],y[3],y[7],y[8] = 2nd simplex.
//
//opposite pairs: (y[4],y[8]),(y[5],y[7]),(y[0],y[6]),
//			(y[1],y[2])
//diagonals: y[3], other is between (0,6), computed by crossdiag(y);
// corners are 0,1,2,6.
//
double solid9(double y[9]);
double dih9_0(double y[9]);
double dih9_1(double y[9]);
double dih9_2(double y[9]);
double dih9_6(double y[9]);
double crossdiag(double y[9]);




// Flyspeck functions:

double interp(double x1,double y1,double x2,double y2,double x);
double hminus();
double h0();
double c1(); // delta0/Pi
double ly(double y) ;
double rho(double y);
double rhazim(double y1,double y2,double y3,double y4,double y5,double y6);
double lnazim(double y1,double y2,double y3,double y4,double y5,double y6);
double azim(double y1,double y2,double y3,double y4,double y5,double y6);
double tau_m(double y1,double y2,double y3,double y4,double y5,double y6);
double tau_m_alt(double y1,double y2,double y3,double y4,double y5,double y6);
double lfun(double h);
double lmfun(double h);
double ell_uvx(double x1,double x2,double x3,double x4,double x5,double x6);

// approximations for y1 derivatives.
double tau_m_diff_quotient(double y1,double y2,double y3,double y4,double y5,double y6);
double tau_m_diff_quotient2(double y1,double y2,double y3,double y4,double y5,double y6);

// a formula for Sqrt[delta] D[taum,y1], valid when delta4 <0, extends to delta->0.
/*
I spent a long time making sure every subexpression corresponds with
the Mathematica calculations and with the interval arithmetic calculations.
It also approximates the results given by difference quotients.  Hopefully,
this is bug-free!
 */
double mdtau(double y1,double y2,double y3,double y4,double y5,double y6);

// a formula for  D[taum,{y1,2}], valid when delta4 <0, delta>0, various u factors >0.
double mdtau2(double y1,double y2,double y3,double y4,double y5,double y6);

// cluster functions
int critical_edge_y(double h) ;
int wtcount6_y(double y1,double y2,double y3,double y4,double y5,double y6);
int wtcount3_y(double y1,double y2,double y3) ;
double bump(double r);
double beta_bump_y(double y1,double y2,double y3,double y4,double y5,double y6);
double machine_eps();


#endif
