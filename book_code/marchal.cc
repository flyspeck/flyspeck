#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// marchal.cc
// $ make marchal.o
// $ ./marchal.o

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

double alphamar = acos(1.0/3.0);
double Kmar = (3.0 * alphamar - pi()) * sqrt(2.0)/(12.0 * pi() - 30.0*alphamar);
double Mmar = (18.0 * alphamar - 7.0*pi())*sqrt(2.0)/(144.0*pi() - 360.0*alphamar);

//Marchal's constants:
double Amar = 0.042692222872;
double Bmar = 0.002652556899;
double Cmar = 0.045574680636;
// second set of Marchal's constants 
double Amarp = 0.049239475726;
double Bmarp = 0.002652556899;
double Cmarp = 0.039027427780;
//

// Marchal's 15 sphere cutoff constant 
//double hmeet = 1.2109264450118509; //where Mfun meets Lfun
//double htmar2 = 1.2486;
//double htmar = 1.3254;

//double hmin = hmeet;
//double hmid = htmar2;
//double hmax = htmar;

double hmin = 1.2317544220903185; // where Mfun meets Lfun
double hmid = 1.26; // 2.52 truncation
double hmax = 1.3254; // zero of Mfun


double interp(double x,double x1,double y1,double x2,double y2) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
double maxx(double a,double b) {
  return (a>b?a:b);
}
double minn(double a,double b) {
  return (a>b?b:a);
}

double Mfun (double r) {
  return (s2 - r)*(r- 1.3254)*(9.0*r*r - 17.0*r + 3.0)/(1.627*(s2- 1.0));
}
double Lfun(double r) {
  return interp(r,  1.0,1.0,    hmid,0.0);
}
double M2fun(double r) {
  return maxx(0,minn(Mfun(r),Lfun(r)));
}

double simplex_vol_y(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sqrt(delta_x(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6))/12.0;
}

double simplex_approx4_Mfun(double y1,double y2,double y3,double y4,double y5,double y6) {
  double d1 = dih_y(y1,y2,y3,y4,y5,y6);
double d2 = dih_y(y2, y3, y1, y5, y6, y4);
double d3 = dih_y(y3, y1, y2, y6, y4, y5);
double d4 = dih_y(y4, y2, y6, y1, y5, y3);
double d5 = dih_y(y5, y3, y4, y2, y6, y1);
double d6 = dih_y(y6, y1, y5, y3, y4, y2);
 return 8.0*((Kmar/(2.0*pi()))*(d1+d2+d3+d4+d5+d6) - Kmar - 
	     (Mmar/pi() )*(d1*Mfun(y1/2.0)+d2*Mfun(y2/2.0)+d3*Mfun(y3/2.0)+
			d4*Mfun(y4/2.0)+d5*Mfun(y5/2.0)+d6*Mfun(y6/2.0)));
}

double simplex_approx4(double y1,double y2,double y3,double y4,double y5,double y6) {
  double d1 = dih_y(y1,y2,y3,y4,y5,y6);
double d2 = dih_y(y2, y3, y1, y5, y6, y4);
double d3 = dih_y(y3, y1, y2, y6, y4, y5);
double d4 = dih_y(y4, y2, y6, y1, y5, y3);
double d5 = dih_y(y5, y3, y4, y2, y6, y1);
double d6 = dih_y(y6, y1, y5, y3, y4, y2);
 return 8.0*((Kmar/(2.0*pi()))*(d1+d2+d3+d4+d5+d6) - Kmar - 
	     (Mmar/pi() )*(d1*M2fun(y1/2.0)+d2*M2fun(y2/2.0)+d3*M2fun(y3/2.0)+
			d4*M2fun(y4/2.0)+d5*M2fun(y5/2.0)+d6*M2fun(y6/2.0)));
}

double gamma4cell (double y1,double y2,double y3,double y4,double y5,double y6) {
  return simplex_vol_y(y1,y2,y3,y4,y5,y6) - simplex_approx4(y1,y2,y3,y4,y5,y6);
}
int wtrange(double t) {
  return ((t >= 2.0*hmin) && (t <= 2.0*hmax));
}
int wtcount(double y1,double y2,double y3,double y4,double y5,double y6) {
  int count =0;
  if (wtrange(y1)) { count++; }
  if (wtrange(y2)) { count++; }
  if (wtrange(y3)) { count++; }
  if (wtrange(y4)) { count++; }
  if (wtrange(y5)) { count++; }
  if (wtrange(y6)) { count++; }
  return count;
}
int wtcount3(double y1,double y2,double y3) {
  int count =0;
  if (wtrange(y1)) { count++; }
  if (wtrange(y2)) { count++; }
  if (wtrange(y3)) { count++; }
  return count;
}
double gamma4wt(double y1,double y2,double y3,double y4,double y5,double y6) {
  gamma4cell(y1,y2,y3,y4,y5,y6)/wtcount(y1,y2,y3,y4,y5,y6);
}


// Now for the 3 variable inequality:
double vol3(double y1,double y2,double y3) {
  return simplex_vol_y(s2,s2,s2,y1,y2,y3);
}
double vol3estimate(double y1,double y2,double y3) {
  double sol1 = sol_y(y1,y2,s2,s2,s2,y3);
  double sol2 = sol_y(y2,y3,s2,s2,s2,y1);
  double sol3 = sol_y(y3,y1,s2,s2,s2,y2);
  double d1 = dih_y(y1,y2,s2,s2,s2,y3);
  double d2 = dih_y(y2,y3,s2,s2,s2,y1);
  double d3 = dih_y(y3,y1,s2,s2,s2,y2);
  return (2.0*Kmar/pi())*(sol1+sol2+sol3) -
    (4.0*Mmar/pi())*2.0*(d1*Mfun(y1/2.0)+d2*Mfun(y2/2.0)+d3*Mfun(y3/2.0));
}
// same using modified M2fun:
double vol3estimate2(double y1,double y2,double y3) {
  double sol1 = sol_y(y1,y2,s2,s2,s2,y3);
  double sol2 = sol_y(y2,y3,s2,s2,s2,y1);
  double sol3 = sol_y(y3,y1,s2,s2,s2,y2);
  double d1 = dih_y(y1,y2,s2,s2,s2,y3);
  double d2 = dih_y(y2,y3,s2,s2,s2,y1);
  double d3 = dih_y(y3,y1,s2,s2,s2,y2);
  return (2.0*Kmar/pi())*(sol1+sol2+sol3) -
    (4.0*Mmar/pi())*2.0*(d1*M2fun(y1/2.0)+d2*M2fun(y2/2.0)+d3*M2fun(y3/2.0));
}
double gamma3cell(double y1,double y2,double y3) {
  if (radf(y1,y2,y3)>sqrt(2.0)) { return 0.0; }
  return vol3(y1,y2,y3) - vol3estimate2(y1,y2,y3);
}
double gamma3wt(double y1,double y2,double y3) {
  return gamma3cell(y1,y2,y3)/wtcount3(y1,y2,y3);
}


// dih*cell2vol(y/2) is the volume of a 2-cell (inside two-stacked Rogers of given dihR).
double cell2vol(double r) {
  return 2*(2 - r*r)*r/6.0;
}
double cell2estimate(double r) {
  return 2*((2*Kmar/pi())*(1-r/s2) - (4*Mmar/pi())*M2fun(r));
}
double gamma2divalpha(double r) {
  return cell2vol(r) - cell2estimate(r);
}
// combined 2 and 3 cell for simplices greater than sqrt2 in rad:
double gg1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double gamma3cellterm =  gamma3cell(y1,y2,y6) + gamma3cell(y1,y3,y5);
  double dihrest = dih_y(y1,y2,y3,y4,y5,y6) - dih_y(y1,y2,s2,s2,s2,y6) - dih_y(y1,y3,s2,s2,s2,y5);
  double cell2 = dihrest*gamma2divalpha(y1/2);
  return cell2 + gamma3cellterm;
}
// wtd combined 2 and 3 cell for simplices greater than sqrt2 in rad:
// assumes that the 2-cell has wt 1 (say, along a supercell)
double ggwt1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double gamma3cellterm =  gamma3wt(y1,y2,y6) + gamma3wt(y1,y3,y5);
  double dihrest = dih_y(y1,y2,y3,y4,y5,y6) - dih_y(y1,y2,s2,s2,s2,y6) - dih_y(y1,y3,s2,s2,s2,y5);
  double cell2 = dihrest*gamma2divalpha(y1/2);
  return cell2 + gamma3cellterm;
}

double dihcc = dih_y(2*hmid,2,2,2,2,2);
double ggcc = gamma4cell(2*hmid,2,2,2,2,2);




//constraint rad < sqrt2:
void smallrad(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
};
//constraint eta_y < s2:
void smallradf(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - (s2);
};
//constraint rady < s2:
void smallrady(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
};
//constraint rady > s2 
void bigrady(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -rady(y[0],y[1],y[2],y[3],y[4],y[5]) + (s2);
};
//constraint rady > s2  rad126, rad135 < s2.
void bigradysmallrafy(int numargs,int whichFn,double* y, double* ret,void*) {
  switch(whichFn) {
  case 1: *ret = -rady(y[0],y[1],y[2],y[3],y[4],y[5]) + (s2); break;
  case 2: *ret = radf(y[0],y[1],y[5]) - (s2); break;
  default: *ret = radf(y[0],y[2],y[4]) - (s2); break;
    
  }
};
//constraint gamma4cell < 0:
void gamma4cell_neg(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]);
};





////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = simplex_vol_y(y[0],y[1],y[2],y[3],y[4],y[5]) -simplex_approx4_Mfun(y[0],y[1],y[2],y[3],y[4],y[5]) + eps;
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t0;
	M.cFunc = smallrad;
	return M;
}
trialdata d0(m0(),"ID d0: Marchal main 4-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol3(y[0],y[1],y[2]) -vol3estimate(y[0],y[1],y[2]) + eps;
	}
Minimizer m1() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradf;
	return M;
}
trialdata d1(m1(),"ID d1: Marchal main 3-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1a(int numargs,int whichFn,double* y, double* ret,void*) {
  double eps = 1.0e-8;
  *ret = gamma3cell(y[0],y[1],y[2])+eps;
	}
Minimizer m1a() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1a;
	M.cFunc = smallradf;
	return M;
}
trialdata d1a(m1a(),"ID GLFVCVK d1: Marchal main 3-cell inequality (M2fun version)");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21a(int numargs,int whichFn,double* y, double* ret,void*) {
  // set to zero on quarters //  
  *ret = (wtcount(y[0],y[1],y[2],y[3],y[4],y[5])==1 ? 0.0 : gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]));
	}
Minimizer m21a() {
  double t = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t21a;
	M.cFunc = smallrad;
	return M;
}
trialdata d21a(m21a(),"ID GLFVCVK: d21: Marchal, gamma4cell(non-quarter) >= 0");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t17(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]) + gamma3cell(y[0],y[1],y[5]);
	}
Minimizer m17() {
  double t = 2.0*hmin-eps;
  double xmin[6]= {2.0*hmin+eps,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t17;
	M.cFunc = smallrady;
	return M;
}
trialdata d17(m17(),"ID FHBVYXZ: cc:2bl: d17: Marchal, 2-blade, gamma4cell(quarter)+gamma3cell>0");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t18(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 1.65 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m18() {
  double t = 2.0*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t18;
	M.cFunc = gamma4cell_neg;
	return M;
}
trialdata d18(m18(),"ID BIXPCGW: cc:3bl: d18: Marchal, dih(quarter) < 1.65, if gamma4cell is neg");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t19(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.8 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m19() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,s8,s8,s8,s8,s8};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t19;
	return M;
}
trialdata d19(m19(),"ID BIXPCGW: cc:3bl: d19: Marchal, dih(four-cell w. diag) < 2.8");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20a() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2.0*hmin,2,2,2,2};
  double xmax[6]= {2.0*hmax,2.0*hmax,s8,s8,s8,s8};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t20a;
	return M;
}
trialdata d20a(m20a(),"ID BIXPCGW: cc:3bl: d20a: Marchal, if wt<1, then angle < 2.3, adjacent");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20b() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2*hmin,2,2};
  double xmax[6]= {2.0*hmax,s8,s8,2*hmax,s8,s8};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t20b;
	return M;
}
trialdata d20b(m20b(),"ID BIXPCGW cc:3bl: d20b: Marchal, if wt<1, then angle < 2.3, opposite");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]) +0.0057;//-ggcc ;
	}
Minimizer m21() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t21;
	return M;
}
trialdata d21(m21(),"ID BIXPCGW: cc:3bl: d21: Marchal, gamma4cell(quarter) > -0.0057");




////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t22(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0057; //ggcc;
	}
//
void c22(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
};
Minimizer m22() {
  double t = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t22;
	M.cFunc = c22;
	return M;
}
trialdata d22(m22(),"ID BIXPCGW: cc:3bl: d22: Marchal, dih > 2.3 ==> gamma4cell() > 0.0057");


double xxmin(int i) {
  if (i==0) { return 2.0; }
  if (i==1) { return 2.0*hmin + eps; }
  return 2*hmax + eps;
}
double xxmax(int i) {
  if (i==0) {return 2*hmin - eps; }
  if (i==1) {return 2.0*hmax - eps; }
  return sqrt(8.0);
}



////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t25(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4wt(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0560305 + 0.0445813 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m25(int i2,int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(i2),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(i2),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t25;
	M.cFunc = smallrady;
	return M;
}
// d25 in main().

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t25a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = ggwt1(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0560305 + 0.0445813 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m25a(int i2,int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(i2),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(i2),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,3,xmin,xmax);
	M.func = t25a;
	M.cFunc = bigradysmallrafy;
	return M;
}
// d25a in main().


int main()
{
double xmin[6];

  // d25 has many cases:
for (int i2=0;i2<3;i2++)
for (int i3=i2;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(i2); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else 
{
trialdata d25(m25(i2,i3,i4,i5,i6),"ID ZTGIJCF: 5:bl: d25: Marchal, gamma4wt >=  0.0560305 - 0.0445813 dih, many cases ");
}
  }

  // d25a has many cases:
for (int i2=0;i2<3;i2++)
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
    xmin[0]=xxmin(1); xmin[1]=xxmin(i2); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
    if (radf(xmin[0],xmin[1],xmin[5])> s2) continue;
    else if (radf(xmin[0],xmin[2],xmin[4])> s2) continue;
    else 
{
trialdata d25a(m25a(i2,i3,i4,i5,i6),"ID ZTGIJCF: 5:bl: d25a: Marchal, ggwt1 >=  0.0560305 - 0.0445813 dih, many cases ");
}
  }

}
