//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifndef ineq_c
#define ineq_c

// These routines use ordinary floating point arithmetic without any
// reference to IEEE-754 standards, rounding modes, interval methods, etc.
// They cannot be used in the rigorous verification of inequalities.
// They can be used to propose and test inequalities that are to be
// proved later by rigorous means.

/* names conforming to definitions_kepler.ml:
pi,pt,delta_x,sol_y,dih_y
 */

double pi();
double pt();
double max(double a,double b);
double min(double a,double b);
double real_pow(double a,double b);
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

// circumradius: 
double eta2(double x1,double x2,double x3);
double radf(double y1,double y2,double y3);
double chi(double x1,double x2,double x3,double x4,double x5,double x6);
double circum2(double x1,double x2,double x3,double x4,double x5,double x6);
double rady(double y1,double y2,double y3,double y4,double y5,double y6);
double arc(double y1,double y2,double y6);
double U(double a,double b,double c);

// terms entering into def'n of VorVc ("A"dih term)
double A_of_vorVc(double h);
double B_of_vorVc(double y);


// scoring:
extern const double doct;
double gamma(double y1,double y2,double y3,double y4,double y5, double y6);
double vor_analytic(double y1,double y2,double y3,double y4,
        double y5,double y6);
double vol_analytic(double y1,double y2,double y3,double y4,
        double y5,double y6);

double tau_analytic(double y1,double y2,double y3,double y4,
        double y5,double y6);
double octavor(double y1,double y2,double y3,double y4,
        double y5,double y6); // average vor_analytic on an upright simplex 
double octavorVc(double y1,double y2,double y3,double y4,
        double y5,double y6); // average VorVc on an upright
//double octatau(double y1,double y2,double y3,double y4,
//        double y5,double y6); // average VorVc on an upright
double vorVc(double y1,double y2,double y3,double y4,
        double y5,double y6);
double vorVc(double y1,double y2,double y3,double y4,double y5,
        double y6,double trunc);
double vorSqc(double y1,double y2,double y3,double y4,
        double y5,double y6);
double tauVc(double y1,double y2,double y3,double y4,
        double y5,double y6);
double tauSqc(double y1,double y2,double y3,double y4,
        double y5,double y6);
double tauVc(double y1,double y2,double y3,double y4,double y5,
        double y6,double trunc);
double tau(double y1,double y2,double y3,double y4,
        double y5,double y6);

double vorNu(double y1,double y2,double y3,double y4,
        double y5,double y6); // octavor +(vorVc-hatvorVc)/2;
double gammaNu(double y1,double y2,double y3,double y4,
        double y5,double y6); // gamma + (vorVc-hatvorVc)/2;
//double tauVnu(double y1,double y2,double y3,double y4,
//        double y5,double y6); // sol zeta pt - vorNu
double tauGnu(double y1,double y2,double y3,double y4,
        double y5,double y6); // sol zeta pt - gammaNu.

double dihVc(double x1,double x2,double x3,double x4,double x5,double x6);
double dihSqc(double x1,double x2,double x3,double x4,double x5,double x6);

// NOTE AUG 2000:
// This is the function called K(S) in FORMULATION-98.
double skelV(double x1,double x2,double x3,double x4,double x5,double x6);
	
double corsigma(double y1,double y2,double y3,double y4,double y5,double y6);
double corsolid(double y1,double y2,double y3,double y4,double y5,double y6);
double cortau(double y1,double y2,double y3,double y4,double y5,double y6);
double sol_cor(double y1,double y2,double y3);



//
double tilde(double h);
double pretilde(double h,double t);
//double crown(double h,double t);
//double crown(double h);
double sfacelift(double y1,double y2,double y6,double t);
double kappa(double y1,double y2,double y3,double y4,double y5,double y6);
double kappa_dih(double y1,double y2,double y3,double y5,double y6,double dih);
double phi(double h,double t);
double quoin(double a,double b,double c);


// rogers:/abc parameters.
double dihR(double a,double b,double c);
double solR(double a,double b,double c);
double vorR(double a,double b,double c);
double volR(double a,double b,double c);
double tauR(double a,double b,double c);

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
double vorVc9(double y[9]);
double solid9(double y[9]);
double dih9_0(double y[9]);
double dih9_1(double y[9]);
double dih9_2(double y[9]);
double dih9_6(double y[9]);
double crossdiag(double y[9]);




// Kepler 2009 functions:

double interp(double x1,double y1,double x2,double y2,double x);
double hminus();
double h0();
double c1(); // delta0/Pi
double ly(double y) ;
double rho(double y);
double rhazim(double y1,double y2,double y3,double y4,double y5,double y6);
double lnazim(double y1,double y2,double y3,double y4,double y5,double y6);
double azim(double y1,double y2,double y3,double y4,double y5,double y6);
double taum(double y1,double y2,double y3,double y4,double y5,double y6);
double taumalt(double y1,double y2,double y3,double y4,double y5,double y6);
double lfun(double h);
double lmfun(double h);

// cluster functions
int critical_edge_y(double h) ;
int wtcount6_y(double y1,double y2,double y3,double y4,double y5,double y6);
int wtcount3_y(double y1,double y2,double y3) ;
double bump(double r);
double beta_bump_y(double y1,double y2,double y3,double y4,double y5,double y6);
double machine_eps();


#endif
