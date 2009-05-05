#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// marchal.cc
// $ make marchal.x
// $ ./marchal.x

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

//functions
//double pi = 4.0*atan(1.0);
double alphamar = acos(1.0/3.0);
double Kmar = (3.0 * alphamar - pi()) * sqrt(2.0)/(12.0 * pi() - 30.0*alphamar);
double Mmar = (18.0 * alphamar - 7.0*pi())*sqrt(2.0)/(144.0*pi() - 360.0*alphamar);
double s2 = sqrt(2.0);
double s8 = sqrt(8.0);

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
//double hmeet = 1.2109264450118509; //where f meets finterp.
//double htmar2 = 1.2486;
//double htmar = 1.3254;

//double hmin = hmeet;
//double hmid = htmar2;
//double hmax = htmar;

double hmin = 1.2317544220903185; // where f meets finterp3
double hmid = 1.26; // 2.52 truncation
double hmax = 1.3254; // zero of f_marchal


double interp(double x,double x1,double y1,double x2,double y2) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
double maxx(double a,double b) {
  return (a>b?a:b);
}
double minn(double a,double b) {
  return (a>b?b:a);
}

double f_marchal (double r) {
  return (s2 - r)*(r- 1.3254)*(9.0*r*r - 17.0*r + 3.0)/(1.627*(s2- 1.0));
}
double f_marchal_interp(double r) {
  return interp(r,  1.0,1.0,    hmid,0.0);
}
double f2_marchal(double r) {
  return maxx(0,minn(f_marchal(r),f_marchal_interp(r)));
}

double simplex_vol_y(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sqrt(delta_x(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6))/12.0;
}

double gammar(double y1,double y2,double y3,double y4,double y5,double y6) {
  double d1 = dih_y(y1,y2,y3,y4,y5,y6);
double d2 = dih_y(y2, y3, y1, y5, y6, y4);
double d3 = dih_y(y3, y1, y2, y6, y4, y5);
double d4 = dih_y(y4, y2, y6, y1, y5, y3);
double d5 = dih_y(y5, y3, y4, y2, y6, y1);
double d6 = dih_y(y6, y1, y5, y3, y4, y2);
 return 8.0*((Kmar/(2.0*pi()))*(d1+d2+d3+d4+d5+d6) - Kmar - 
	     (Mmar/pi() )*(d1*f_marchal(y1/2.0)+d2*f_marchal(y2/2.0)+d3*f_marchal(y3/2.0)+
			d4*f_marchal(y4/2.0)+d5*f_marchal(y5/2.0)+d6*f_marchal(y6/2.0)));
}

double gammar2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double d1 = dih_y(y1,y2,y3,y4,y5,y6);
double d2 = dih_y(y2, y3, y1, y5, y6, y4);
double d3 = dih_y(y3, y1, y2, y6, y4, y5);
double d4 = dih_y(y4, y2, y6, y1, y5, y3);
double d5 = dih_y(y5, y3, y4, y2, y6, y1);
double d6 = dih_y(y6, y1, y5, y3, y4, y2);
 return 8.0*((Kmar/(2.0*pi()))*(d1+d2+d3+d4+d5+d6) - Kmar - 
	     (Mmar/pi() )*(d1*f2_marchal(y1/2.0)+d2*f2_marchal(y2/2.0)+d3*f2_marchal(y3/2.0)+
			d4*f2_marchal(y4/2.0)+d5*f2_marchal(y5/2.0)+d6*f2_marchal(y6/2.0)));
}

double gg (double y1,double y2,double y3,double y4,double y5,double y6) {
  return simplex_vol_y(y1,y2,y3,y4,y5,y6) - gammar2(y1,y2,y3,y4,y5,y6);
}
double eps = 1.0e-14;
int wtrange(double t) {
  return ((t >= 2.0*hmin) && (t <= 2.0*hmax));
}
double wt(double y1,double y2,double y3,double y4,double y5,double y6) {
  int count =0;
  if (wtrange(y1)) { count++; }
  if (wtrange(y2)) { count++; }
  if (wtrange(y3)) { count++; }
  if (wtrange(y4)) { count++; }
  if (wtrange(y5)) { count++; }
  if (wtrange(y6)) { count++; }
  return count;
}
double ggw(double y1,double y2,double y3,double y4,double y5,double y6) {
  gg(y1,y2,y3,y4,y5,y6)/wt(y1,y2,y3,y4,y5,y6);
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
    (4.0*Mmar/pi())*2.0*(d1*f_marchal(y1/2.0)+d2*f_marchal(y2/2.0)+d3*f_marchal(y3/2.0));
}
// same using modified f2_marchal:
double vol3estimate2(double y1,double y2,double y3) {
  double sol1 = sol_y(y1,y2,s2,s2,s2,y3);
  double sol2 = sol_y(y2,y3,s2,s2,s2,y1);
  double sol3 = sol_y(y3,y1,s2,s2,s2,y2);
  double d1 = dih_y(y1,y2,s2,s2,s2,y3);
  double d2 = dih_y(y2,y3,s2,s2,s2,y1);
  double d3 = dih_y(y3,y1,s2,s2,s2,y2);
  return (2.0*Kmar/pi())*(sol1+sol2+sol3) -
    (4.0*Mmar/pi())*2.0*(d1*f2_marchal(y1/2.0)+d2*f2_marchal(y2/2.0)+d3*f2_marchal(y3/2.0));
}
double vv(double y1,double y2,double y3) {
  if (radf(y1,y2,y3)>sqrt(2.0)) { return 0.0; }
  return vol3(y1,y2,y3) - vol3estimate2(y1,y2,y3);
}
// dih*cell2vol(y/2) is the volume of a 2-cell (inside a Rogers of given dihR).
double cell2vol(double r) {
  return (2 - r*r)*r/6.0;
}
double cell2estimate(double r) {
  return (2*Kmar/pi())*(1-r/s2) - (4*Mmar/pi())*f2_marchal(r);
}
// combined 2 and 3 cell for simplices greater than sqrt2 in rad:
double gg1(double y1,double y2,double y3,double y4,double y5,double y6) {
  double vvterm =  vv(y1,y2,y6) + vv(y1,y3,y5);
  double dihrest = dih_y(y1,y2,y3,y4,y5,y6) - dih_y(y1,y2,s2,s2,s2,y6) - dih_y(y1,y3,s2,s2,s2,y5);
  double cell2 = dihrest*(cell2vol(y1/2) - cell2estimate(y1/2));
  return cell2 + vvterm;
}

double dihcc = dih_y(2*hmid,2,2,2,2,2);
double ggcc = gg(2*hmid,2,2,2,2,2);




//constraint rad < sqrt2:
void smallrad(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
};
//constraint eta_y < s2 - eps:
void smallradf(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = radf(y[0],y[1],y[2]) - (s2);
};
//constraint rady < s2 - eps:
void smallrady(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2);
};
//constraint rady > s2 
void bigrady(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = -rady(y[0],y[1],y[2],y[3],y[4],y[5]) + (s2);
};
//constraint gg < 0:
void gg_neg(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg(y[0],y[1],y[2],y[3],y[4],y[5]);
};





////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = simplex_vol_y(y[0],y[1],y[2],y[3],y[4],y[5]) -gammar(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0;
	M.cFunc = smallrad;
	return M;
}
trialdata d0(m0(),"ID d0: Marchal main inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0_1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m0_1() {
  double xmin[6]= {2*hmax+eps,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_1(m0_1(),"ID d0_01: Marchal GGPOS f2 function, one above hmax");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2*hmin,2*hmin,2*hmin,2*hmin,2*hmin,2*hmin};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_2(m0_2(),"ID d0_2: Marchal GGPOS f2 function, all below hmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_3() {
  double xmin[6]= {2*hmin,2,2,2*hmin,2,2};
  double xmax[6]= {2*hmax,2*hmax,2*hmax,2*hmax,2*hmax,2*hmax};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_3(m0_3(),"ID d0_3: Marchal GGPOS f2 function, opposite pair above hmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_4() {
  double xmin[6]= {2*hmin,2*hmin,2,2,2,2};
  double xmax[6]= {2*hmax,2*hmax,2*hmax,2*hmax,2*hmax,2*hmax};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_4(m0_4(),"ID d0_4: Marchal GGPOS f2 function, adjacent pair above hmin");



////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol3(y[0],y[1],y[2]) -vol3estimate(y[0],y[1],y[2]);
	}
Minimizer m1() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(8000,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradf;
	return M;
}
trialdata d1(m1(),"ID d1: Marchal 3D inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t17(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg(y[0],y[1],y[2],y[3],y[4],y[5]) + vv(y[0],y[1],y[5]);
	}
Minimizer m17() {
  double t = 2.0*hmin-eps;
  double xmin[6]= {2.0*hmin+eps,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t17;
	M.cFunc = smallrady;
	return M;
}
trialdata d17(m17(),"ID d17: Marchal, 15-spheres, gg+vv");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t18(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 1.65 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m18() {
  double t = 2.0*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t18;
	M.cFunc = gg_neg;
	return M;
}
trialdata d18(m18(),"ID d18: Marchal, dih(quarter) < 1.65, if gg is neg");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t19(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.8 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m19() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,s8,s8,s8,s8,s8};
	Minimizer M(80,6,0,xmin,xmax);
	M.func = t19;
	return M;
}
trialdata d19(m19(),"ID d19: Marchal, dih(four-cell w. diag) < 2.8");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20a() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2.0*hmin,2,2,2,2};
  double xmax[6]= {2.0*hmax,2.0*hmax,s8,s8,s8,s8};
	Minimizer M(80,6,0,xmin,xmax);
	M.func = t20a;
	return M;
}
trialdata d20a(m20a(),"ID d20a: Marchal, if wt>1, then angle < 2.3, adjacent");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20b() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2*hmin,2,2};
  double xmax[6]= {2.0*hmax,s8,s8,2*hmax,s8,s8};
	Minimizer M(80,6,0,xmin,xmax);
	M.func = t20b;
	return M;
}
trialdata d20b(m20b(),"ID d20b: Marchal, if wt>1, then angle < 2.3, opposite");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg(y[0],y[1],y[2],y[3],y[4],y[5]) -ggcc ;
	}
Minimizer m21() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(80,6,0,xmin,xmax);
	M.func = t21;
	return M;
}
trialdata d21(m21(),"ID d21: Marchal, gg(quarter) > ggcc");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t22(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg(y[0],y[1],y[2],y[3],y[4],y[5]) + ggcc;
	}
//
void c22(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
};
Minimizer m22() {
  double t = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t22;
	M.cFunc = c22;
	return M;
}
trialdata d22(m22(),"ID d22: Marchal, dih > 2.3 ==> gg() > - ggcc");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t23(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg1(y[0],y[1],y[2],y[3],y[4],y[5]) - (0.2147) + 0.20495 * (dih_y(y[0],y[1],y[2],y[3],y[4],y[5]));
	}
Minimizer m23() {
  double t = 2.0*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,sqrt(8.0),t,t};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t23;
	M.cFunc = bigrady;
	return M;
}
trialdata d23(m23(),"ID d23: Marchal, vv >= 0.2147/2 - 0.20495 dih");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t24(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = ggw(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.2147 + 0.20495 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
double m24m(int i) {
  if (i==0) { return 2.0; }
  if (i==1) { return 2.0*hmin + eps; }
  return 2*hmax + eps;
}
double m24x(int i) {
  if (i==0) {return 2*hmin - eps; }
  if (i==1) {return 2.0*hmax - eps; }
  return sqrt(8.0);
}
Minimizer m24(int i2,int i3,int i4,int i5,int i6) {
  double xmin[6]= {m24m(1),m24m(i2),m24m(i3),m24m(i4),m24m(i5),m24m(i6)};
  double xmax[6]= {m24x(1),m24x(i2),m24x(i3),m24x(i4),m24x(i5),m24x(i6)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t24;
	M.cFunc = smallrady;
	return M;
}
// d24 in main().


int main()
{
  // LEAVE EMPTY.
  // d24 has many cases:
  /*
for (int i2=0;i2<3;i2++)
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
trialdata d24(m24(i2,i3,i4,i5,i6),"ID d24: Marchal, ggw >=  0.2147 - 0.2045 dih, many cases ");
  }
  */

}
