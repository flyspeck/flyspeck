#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// marchal.cc
// $ make marchal.o
// $ ./marchal.o

// bump added 7/24/09

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

double hmin = 1.2317544220903185; // where Mfun meets Lfun
double hmid = 1.26; // 2.52 truncation
double h0 = 1.26;
double hmax = 1.3254; // zero of Mfun


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

// experimental bump function.
double bump(double r) { 
  double s = (r-h0)/(hmax-h0);
  return 1.0 - s*s;
}
double bmpfactor = 0.005;
double bmp2(double y1,double y4) {
  return bmpfactor*(bump(y1/2.0) - bump(y4/2.0));
}
double bmp(double y1,double y2,double y3,double y4,double y5,double y6) {
  if (2!=wtcount(y1,y2,y3,y4,y5,y6))  { return 0.0; }
  if (!wtrange(y1))  { return 0.0; }
  if (!wtrange(y4))  { return 0.0; }
  return bmp2(y1,y4);
}

/* moved to numerical.cc
double interp(double x1,double y1,double x2,double y2,double x) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}
*/

double Mfun (double r) {
  return (s2 - r)*(r- 1.3254)*(9.0*r*r - 17.0*r + 3.0)/(1.627*(s2- 1.0));
}

double Lfun(double r) {
  return interp(  1.0,1.0,    hmid,0.0,  r);
}

double Lmfun(double r) {
  return max(0,Lfun(r));
}

double vol4(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sqrt(delta_x(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6))/12.0;
}

double vol4M(double y1,double y2,double y3,double y4,double y5,double y6) {
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

double vol4L(double y1,double y2,double y3,double y4,double y5,double y6) {
  double d1 = dih_y(y1,y2,y3,y4,y5,y6);
double d2 = dih_y(y2, y3, y1, y5, y6, y4);
double d3 = dih_y(y3, y1, y2, y6, y4, y5);
double d4 = dih_y(y4, y2, y6, y1, y5, y3);
double d5 = dih_y(y5, y3, y4, y2, y6, y1);
double d6 = dih_y(y6, y1, y5, y3, y4, y2);
 return 8.0*((Kmar/(2.0*pi()))*(d1+d2+d3+d4+d5+d6) - Kmar - 
	     (Mmar/pi() )*(d1*Lmfun(y1/2.0)+d2*Lmfun(y2/2.0)+d3*Lmfun(y3/2.0)+
			d4*Lmfun(y4/2.0)+d5*Lmfun(y5/2.0)+d6*Lmfun(y6/2.0)));
}

double gamma4L (double y1,double y2,double y3,double y4,double y5,double y6) {
  return vol4(y1,y2,y3,y4,y5,y6) - vol4L(y1,y2,y3,y4,y5,y6);
}

double gamma4Lbwt(double y1,double y2,double y3,double y4,double y5,double y6) {
  return gamma4L(y1,y2,y3,y4,y5,y6)/wtcount(y1,y2,y3,y4,y5,y6) 
    + bmp(y1,y2,y3,y4,y5,y6);
}
double gamma4Lbump(double y1,double y2,double y3,double y4,double y5,double y6) {
  return gamma4L(y1,y2,y3,y4,y5,y6)/2.0
    + bmp(y1,y2,y3,y4,y5,y6);
}




// Now for the 3 variable inequality:
double vol3(double y1,double y2,double y3) {
  return vol4(s2,s2,s2,y1,y2,y3);
}
double vol3M(double y1,double y2,double y3) {
  double sol1 = sol_y(y1,y2,s2,s2,s2,y3);
  double sol2 = sol_y(y2,y3,s2,s2,s2,y1);
  double sol3 = sol_y(y3,y1,s2,s2,s2,y2);
  double d1 = dih_y(y1,y2,s2,s2,s2,y3);
  double d2 = dih_y(y2,y3,s2,s2,s2,y1);
  double d3 = dih_y(y3,y1,s2,s2,s2,y2);
  return (2.0*Kmar/pi())*(sol1+sol2+sol3) -
    (4.0*Mmar/pi())*2.0*(d1*Mfun(y1/2.0)+d2*Mfun(y2/2.0)+d3*Mfun(y3/2.0));
}
// same using modified Lmfun:
double vol3L(double y1,double y2,double y3) {
  double sol1 = sol_y(y1,y2,s2,s2,s2,y3);
  double sol2 = sol_y(y2,y3,s2,s2,s2,y1);
  double sol3 = sol_y(y3,y1,s2,s2,s2,y2);
  double d1 = dih_y(y1,y2,s2,s2,s2,y3);
  double d2 = dih_y(y2,y3,s2,s2,s2,y1);
  double d3 = dih_y(y3,y1,s2,s2,s2,y2);
  return (2.0*Kmar/pi())*(sol1+sol2+sol3) -
    (4.0*Mmar/pi())*2.0*(d1*Lmfun(y1/2.0)+d2*Lmfun(y2/2.0)+d3*Lmfun(y3/2.0));
}
double gamma3L(double y1,double y2,double y3) {
  if (radf(y1,y2,y3)>sqrt(2.0)) { return 0.0; }
  return vol3(y1,y2,y3) - vol3L(y1,y2,y3);
}
double gamma3Lwt(double y1,double y2,double y3) {
  return gamma3L(y1,y2,y3)/wtcount3(y1,y2,y3);
}


// dih*vol2(y/2) is the volume of a 2-cell (inside two-stacked Rogers of given dihR).
double vol2(double r) {
  return 2*(2 - r*r)*r/6.0;
}
double vol2L(double r) {
  return 2*((2*Kmar/pi())*(1-r/s2) - (4*Mmar/pi())*Lmfun(r));
}
double gamma2Ldivalpha(double r) {
  return vol2(r) - vol2L(r);
}
// combined 2 and 3 cell for simplices greater than sqrt2 in rad:
double gamma23L(double y1,double y2,double y3,double y4,double y5,double y6) {
  double gamma3Lterm =  gamma3L(y1,y2,y6) + gamma3L(y1,y3,y5);
  double dihrest = dih_y(y1,y2,y3,y4,y5,y6) - dih_y(y1,y2,s2,s2,s2,y6) - dih_y(y1,y3,s2,s2,s2,y5);
  double cell2 = dihrest*gamma2Ldivalpha(y1/2);
  return cell2 + gamma3Lterm;
}
// wtd combined 2 and 3 cell for simplices greater than sqrt2 in rad:
// assumes that the 2-cell has wt 1 (say, along a supercell)
double gamma23Lwt(double y1,double y2,double y3,double y4,double y5,double y6) {
  double gamma3Lterm =  gamma3Lwt(y1,y2,y6) + gamma3Lwt(y1,y3,y5);
  double dihrest = dih_y(y1,y2,y3,y4,y5,y6) - dih_y(y1,y2,s2,s2,s2,y6) - dih_y(y1,y3,s2,s2,s2,y5);
  double cell2 = dihrest*gamma2Ldivalpha(y1/2);
  return cell2 + gamma3Lterm;
}

//double dihcc = dih_y(2*hmid,2,2,2,2,2); global min of gamma3L.
//double ggcc = gamma4L(2*hmid,2,2,2,2,2);




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
}







////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol4(y[0],y[1],y[2],y[3],y[4],y[5]) -vol4M(y[0],y[1],y[2],y[3],y[4],y[5]) + eps;
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t0;
	M.cFunc = smallrad;
	return M;
}
trialdata d0(m0(),"ID[1025009205] d0: Marchal main 4-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol3(y[0],y[1],y[2]) -vol3M(y[0],y[1],y[2]) + eps;
	}
Minimizer m1() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradf;
	return M;
}
trialdata d1(m1(),"ID[3564312720] d1: Marchal main 3-cell inequality");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t1a(int numargs,int whichFn,double* y, double* ret,void*) {
  double eps = 1.0e-7;
  *ret = gamma3L(y[0],y[1],y[2])+eps;
	}
Minimizer m1a() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1a;
	M.cFunc = smallradf;
	return M;
}
trialdata d1a(m1a(),"ID[4869905472] GLFVCVK d1a: Marchal main 3-cell inequality (L version) \n (Exact equality when eta=sqrt2)");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21a(int numargs,int whichFn,double* y, double* ret,void*) {
  // set to zero on quarters //  
  //*ret = (wtcount(y[0],y[1],y[2],y[3],y[4],y[5])==1 ? 0.0 : gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]));
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
//constraint outside a ball (which is contained in quarters), rad < sqrt2
void c21a(int numargs,int whichFn,double* y, double* ret,void*) {
  double hh = (hmin + hmax)/2.0;
  double z[6]={2*hh,2,2,2,2,2};
  double r0 = 4.0*(hmax-hh)*(hmax-hh);
  double r = 0.0;
  for (int i=0;i<6;i++) { r += (y[i]-z[i])*(y[i]-z[i]); }
  switch(whichFn) {
  case 1 : *ret =rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (s2); break;
  case 2: *ret  = - r + r0; break;
    // if not a quarter then some |yi-zi|^2 > r0
  }
}
Minimizer m21a() {
  double t = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,2,xmin,xmax);
	M.func = t21a;
	M.cFunc = c21a;
	return M;
}
trialdata d21a(m21a(),"ID[2477216213] GLFVCVK: d21: Marchal, gamma4L(non-quarter) >= 0");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m21b() {
  double ep = 1.0e-5;
  double t = 2*hmin-ep;
  double xmin[6]= {2.0*hmin+ep,2,2,2*hmin+ep,2,2};
  double xmax[6]= {2.0*hmax-ep,t,t,2*hmax-ep,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t21b;
	M.cFunc = smallrady;
	return M;
}
trialdata d21b(m21b(),"ID[8328676778] GLFVCVK d21b: Marchal, gamma4Lbwt(4cell wt2 opp) >= 0");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t17(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) + gamma3L(y[0],y[1],y[5]);
	}
Minimizer m17() {
  double t = 2.0*hmin-eps;
  double xmin[6]= {2.0*hmin+eps,2,2,2,2,2};
  double xmax[6]= {2.0*hmax-eps,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t17;
	M.cFunc = smallrady;
	return M;
}
trialdata d17(m17(),"ID[1118115412] FHBVYXZ: cc:2bl: d17: Marchal, 2-blade, gamma4L(quarter)+gamma3L>0");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void c18(int numargs,int whichFn,double* y, double* ret,void*) {
      *ret = 1.65 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]); 
 	}
void t18(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m18() {
  double t = 2.0*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t18;
	M.cFunc = c18;
	return M;
}
trialdata d18(m18(),"ID[2300537674] BIXPCGW: cc:3bl: d18: Marchal, dih(quarter) < 1.65, if gamma4L is neg");

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
trialdata d19(m19(),"ID[6652007036] BIXPCGW: cc:3bl: d19: Marchal, dih(four-cell along spine) < 2.8");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20a() {
  double s8 = sqrt(8.0);
  double xmin[6]= {2.0*hmin,2.0*hmin,2,2,2,2};
  //  double xmax[6]= {2.0*hmax,2.0*hmax,s8,s8,s8,s8};
  double xmax[6]= {2.0*hmax,s8,s8,s8,s8,s8};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t20a;
	return M;
}
trialdata d20a(m20a(),"ID[7080972881] BIXPCGW: cc:3bl: d20a: Marchal, if wt<1, then angle < 2.3, adjacent");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t20b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.3 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m20b() {
  double s8 = sqrt(8.0);
  //  double xmin[6]= {2.0*hmin,2,2,2*hmin,2,2};
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,s8,s8,2*hmax,s8,s8};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t20b;
	return M;
}
trialdata d20b(m20b(),"ID[1738910218] BIXPCGW cc:3bl: d20b: Marchal, if wt<1, then angle < 2.3, opposite");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t21(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) +0.00569;//-ggcc ;
	}
Minimizer m21() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t21;
	return M;
}
trialdata d21(m21(),"ID[9455898160] BIXPCGW: cc:3bl: d21: Marchal, gamma4L(quarter) > -0.00569");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t41a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) + 0.00259 ;
	}
Minimizer m41a() {
  double t = 2*hmin;
  double xmin[6]= {2.58,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t41a;
	return M;
}
trialdata d41a(m41a(),"ID[] : cc:4bl: d41a: Marchal, gamma4L(quarter with y1>2.58) > -0.00259");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t41b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.007771 ;
	}
Minimizer m41b() {
  double t = 2*hmin;
  double e=1.0e-8;
  double xmin[6]= {2.57,2,2,2*hmin+e,2,2};
  double xmax[6]= {2.0*hmax-e,t,t,2*hmax-e,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t41b;
	return M;
}
trialdata d41b(m41b(),"ID[] : cc:4bl: d41b: Marchal, gamma4Lbwt(halfwt with y1>2.58) > 0.007771");




////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t22(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0057; 
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
trialdata d22(m22(),"ID[7274157868] BIXPCGW: cc:3bl: d22: Marchal, dih > 2.3 ==> gamma4L() > 0.0057");


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
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0560305 + 0.0445813 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
/* eta(2hmin,2hmin,2hmin) >sqrt2. so one of the edges adjacent
    to the spine is in the range [2,2hmin].
    WLOG it is the edge y[1].
*/
Minimizer m25(int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t25;
	M.cFunc = smallrady;
	return M;
}
// d25 in main().

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t25a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma23Lwt(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.0560305 + 0.0445813 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
// See t25 for explanation of why we use xxmin(0) xxmax(0). for y[1].
Minimizer m25a(int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,3,xmin,xmax);
	M.func = t25a;
	M.cFunc = bigradysmallrafy;
	return M;
}
// d25a in main().

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t26(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) + 0.0659 - dih_y(y[0],y[1],y[2],y[3],y[4],y[5])*0.042;
	}
//
Minimizer m26() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t26;
	return M;
}
trialdata d26(m26(),"ID[5653753305] QITNPEA: cc:4bl: d26: Marchal, 4blades j=4 quarters");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t27(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 
    gamma4Lbwt(y[0],y[1],y[2],   y[3],y[4],y[5]) // #Ec(X) = 2.  wt=1/2.
    +gamma4L(y[0],y[1],y[6],   y[8],y[7],y[5])
   +gamma4L(y[0],y[10],y[6], y[9],y[7],y[11])
    +gamma4L(y[0],y[10],y[2], y[12],y[4],y[11]);
	}
//constraint dih > 2pi  
void c27(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 2.0*pi() 
    - dih_y(y[0],y[1],y[2],   y[3],y[4],y[5])
    - dih_y(y[0],y[1],y[6],   y[8],y[7],y[5])
    - dih_y(y[0],y[10],y[6], y[9],y[7],y[11])
    - dih_y(y[0],y[10],y[2], y[12],y[4],y[11]);
  }
//
Minimizer m27() {
  double t = 2*hmin-eps;
  double w1 = 2*hmin+eps;
  double w2 = 2*hmax-eps;
  double xmin[13]= {w1,2,2,    w1,2,2,  2,2,2,    2,2,2,    2};
  double xmax[13]= {w2,t,t,      w2,t,t,   t,t,t,        t,t,t,       t};
  Minimizer M(trialcount /* * 40 */,13,1,xmin,xmax);
	M.func = t27;
	M.cFunc = c27;
	return M;
}
trialdata d27(m27(),"ID[] d27: Marchal, 4blades j=3 quarters, full version");

double ajp(double a,double b,double j) {
  return (j*a+ 2.0*pi()*b)/(j-2.0);
}
double a1  = 0.00127562;
double b1 = -0.00522841;
double a1p = ajp(a1,b1,1.0);
double a2 = 0.161517;
double b2 = -0.119482;
double a2p = ajp(a2,b2,2.0);
double a3 = -0.0142852;
double b3 = 0.00609451;
double a3p = ajp(a3,b3,3.0);


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t28(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) 
     - 0.00457511 - 0.00609451*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - ajp(a3,b3,3) - b3*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
//
Minimizer m28() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2.0*hmax,2,2};
  double xmax[6]= {2.0*hmax,t,t,s8,t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t28;
	M.cFunc = smallrady;
	return M;
}
trialdata d28(m28(),"ID[9939613598] QITNPEA: cc:4bl: d28: Marchal, 4blades j=3 quarters, wt1 complement");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t30(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma23Lwt(y[0],y[1],y[2],y[3],y[4],y[5]) 
     - 0.00457511 - 0.00609451*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - ajp(a3,b3,3) - b3*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
//
Minimizer m30() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2.0*hmax,2,2};
  double xmax[6]= {2.0*hmax,t,t,s8,t,t};
	Minimizer M(trialcount,6,3,xmin,xmax);
	M.func = t30;
	M.cFunc = bigradysmallrafy;
	return M;
}
trialdata d30(m30(),"ID[4003532128] QITNPEA: cc:4bl: d30: Marchal, 4blades j=3 quarters, 2-cell,3-cell complement");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t29(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) 
   +0.0142852 - 0.00609451*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - a3 - b3*dih 
	}
//
Minimizer m29() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t29;
	M.cFunc = smallrady;
	return M;
}
trialdata d29(m29(),"ID[6206775865] QITNPEA: cc:4bl: d29: Marchal, 4blades j=3 quarters, quarter ineq");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t31(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) 
    -0.00127562 + 0.00522841*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - a1 - b1*dih
	}
//
Minimizer m31() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t31;
	M.cFunc = smallrady;
	return M;
}
trialdata d31(m31(),"ID[5814748276] QITNPEA: cc:4bl: d31: Marchal, 4blades j=1 quarters, quarter ineq");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t32(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) 
    -0.0105256 +  0.00522841*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - ajp(a1,b1,1) - b1*dih
	}
Minimizer m32(int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t32;
	M.cFunc = smallrady;
	return M;
}
//see main()



////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t34(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) -0.0057;
	}
// in 2quarter case, one blade is shared with a quarter constraining sides.
//In this case other blade is not along a quarter and has a long edge.
Minimizer m34(int i3,int i4) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(i3),xxmin(i4),xxmin(0),xxmin(0)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(i3),xxmax(i4),xxmax(0),xxmax(0)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t34;
	M.cFunc = smallrady;
	return M;
}
// see main

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t35(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) 
    -0.161517 + 0.119482*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // -a2 - b2*dih
	}
//
Minimizer m35() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,t,t,t};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t35;
	M.cFunc = smallrady;
	return M;
}
trialdata d35(m35(),"ID[3848804089] QITNPEA: cc:4bl: d35: Marchal, 4blades j=2 quarters, quarter ineq, small blade case");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t36(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) 
    -0.213849 + 0.119482*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
  // - ajp(b2,b2,2) - b2*dih.
	}
// in 2quarter case, one blade is shared with a quarter constraining sides.
//In this case other blade is not along a quarter and has a long edge.
Minimizer m36(int i4) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(0),xxmin(i4),xxmin(0),xxmin(0)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(0),xxmax(i4),xxmax(0),xxmax(0)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t36;
	M.cFunc = smallrady;
	return M;
}
// see main

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t36b(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbwt(y[0],y[1],y[2],y[3],y[4],y[5]) +
    gamma3L(y[0],y[1],y[5]) - 0.0057;
	}
Minimizer m36b(int i4) {
  double xmin[6]= {xxmin(1),xxmin(0),xxmin(0),xxmin(i4),xxmin(0),xxmin(0)};
  double xmax[6]= {xxmax(1),xxmax(0),xxmax(0),xxmax(i4),xxmax(0),xxmax(0)}; 
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t36b;
	M.cFunc = smallrady;
	return M;
}
// see main

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t36a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma23L(y[0],y[1],y[2],y[3],y[4],y[5]) - 2.0*0.0057;
	}
Minimizer m36a() {
  double t = 2*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,s8,t,t};
	Minimizer M(trialcount*40,6,3,xmin,xmax);
	M.func = t36a;
	M.cFunc = bigradysmallrafy; 
	return M;
}
//false:  trialdata d36a(m36a(),"ID[] QITNPEA: cc:4bl: d36a: Marchal, 4blades j=1 or 2 quarters, 23cell ineq, small blade case");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t37(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = taum(y[0],y[1],y[2],y[3],y[4],y[5]) +
    taum(y[0],y[2],y[6],y[7],y[8],y[4]) +
    taum(y[0],y[6],y[9],y[10],y[11],y[8]) +
    taum(y[0],y[9],y[12],y[13],y[14],y[11]) +
    taum(y[0],y[12],y[15],y[16],y[17],y[14]) +
    taum(y[0],y[15],y[1],y[18],y[5],y[17]);
	}
//constraint rady > s2 
void c37(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = 
 dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) +
    dih_y(y[0],y[2],y[6],y[7],y[8],y[4]) +
    dih_y(y[0],y[6],y[9],y[10],y[11],y[8]) +
    dih_y(y[0],y[9],y[12],y[13],y[14],y[11]) +
    dih_y(y[0],y[12],y[15],y[16],y[17],y[14]) +
   dih_y(y[0],y[15],y[1],y[18],y[5],y[17]) - 2.0*pi();
};
Minimizer m37() {
  double s = 2.52;
  double xmin[19]= {2,2,2,2,2,2,  2,2,2,2,2,2,  2,2,2,2,2,2,  2};
  double xmax[19]= {s,s,s,s,s,s,  s,s,s,s,s,s,  s,s,s,s,s,s,  s  };
	Minimizer M(trialcount,19,1,xmin,xmax);
	M.func = t37;
	M.cFunc = c37;
	return M;
}
//trialdata d37(m37(),"test of squander on vertex of type 600");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
double e38=0;
double a38=0;
double bq38=0;
double bh38=0;
double dq38=0;
double dh38=0;
void t38q(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4L(y[0],y[1],y[2],y[3],y[4],y[5]) +
     a38*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) +
    bq38*y[0] + dq38;

	}
void t38h(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4Lbump(y[0],y[1],y[2],y[3],y[4],y[5]) +
     a38*dih_y(y[0],y[1],y[2],y[3],y[4],y[5]) +
    bh38*y[0] + dh38;
	}
double conv(double r,double s,double a,double b) {
  return r*a + s*b;
}
Minimizer m38q(double* mdata) {
  double r,s,a,b;
  e38 = mdata[0];
  a38 = mdata[1];
  bq38=mdata[2];
  bh38=mdata[3];
  dq38=mdata[4];
  dh38=mdata[5];
  double y1min = conv(mdata[6],mdata[9],mdata[7],mdata[8]);
  double y1max = conv(mdata[6],mdata[9],mdata[10],mdata[11]);
  double y4qmin=conv(mdata[12],mdata[15],mdata[13],mdata[14]);
  double y4qmax=conv(mdata[12],mdata[15],mdata[16],mdata[17]);
  double xmin[6]= {y1min,2,2,y4qmin,2,2};
  double xmax[6]={y1max,2*hmin,2*hmin,y4qmax,2*hmin,2*hmin};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t38q;
	return M;
}
Minimizer m38h(double* mdata) {
  double r,s,a,b;
  e38 = mdata[0];
  a38 = mdata[1];
  bq38=mdata[2];
  bh38=mdata[3];
  dq38=mdata[4];
  dh38=mdata[5];
  double y1min = conv(mdata[6],mdata[9],mdata[7],mdata[8]);
  double y1max = conv(mdata[6],mdata[9],mdata[10],mdata[11]);
  double y4hmin=conv(mdata[18],mdata[21],mdata[19],mdata[20]);
  double y4hmax=conv(mdata[18],mdata[21],mdata[22],mdata[23]);
  double xmin[6]= {y1min,2,2,y4hmin,2,2};
  double xmax[6]={y1max,2*hmin,2*hmin,y4hmax,2*hmin,2*hmin};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t38h;
	return M;
}
double md1[38]={-0.028864, 0.202002, -0.183386, 0.550157,
   0.149274, -1.71704, 2.52, 1., 0., 2.6508, 0., 1., 2., 0.5, 0.5,
		2.46351, 0., 1., 2.46351, 1., 0., 2.52, 0., 1.};
trialdata d38_md1q(m38q(md1),"md1 experimental test of gamma4L(quarter)+... 4blade, 3 quarter.");
trialdata d38_md1h(m38h(md1),"md1 experimental test of gamma4Lbump(halfwt)+... 4blade, 3 quarter.");


int main()
{
double xmin[6];
 double docases=0;

  // d25 has many cases:
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else 
{
  if (docases) { trialdata d25(m25(i3,i4,i5,i6),"ID[1821661595] ZTGIJCF: 5:bl: d25: Marchal, gamma4Lbwt >=  0.0560305 - 0.0445813 dih, many cases "); }
}
  }

  // d25a has many cases:
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
    xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
    if (radf(xmin[0],xmin[1],xmin[5])> s2) continue;
    else if (radf(xmin[0],xmin[2],xmin[4])> s2) continue;
    else 
{
  if (docases) { trialdata d25a(m25a(i3,i4,i5,i6),"ID[7907792228] ZTGIJCF: 5:bl: d25a: Marchal, gamma23Lwt >=  0.0560305 - 0.0445813 dih, many cases "); }
}
  }


for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
 else if (!(i3+i4+i5+i6)) continue; // skip quarter case.
else
{
  if (docases) { trialdata d32(m32(i3,i4,i5,i6),"ID[3803737830] QITNPEA: cc:4bl: d32: Marchal, 4blades j=1 quarters, 4-cell bwt"); }
}
  }





for (int i3=1;i3<3;i3++)
for (int i4=0;i4<3;i4++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(0); xmin[5]=xxmin(0);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else
{
  if (docases) { trialdata d34(m34(i3,i4),"ID[9063653052] QITNPEA: cc:4bl: d34: Marchal, 4blades j=2 quarters, 4-cell bwt, long edge adjacent to spine"); }
}
  }


for (int i4=1;i4<3;i4++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(0); xmin[3]=xxmin(i4); xmin[4]=xxmin(0); xmin[5]=xxmin(0);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else
{
  if (docases) { trialdata d36(m36(i4),"ID[2134082733] QITNPEA: cc:4bl: d36: Marchal, 4blades j=2 quarters, 4-cell bwt, small blades"); }
}
  }

for (int i4=1;i4<3;i4++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(0); xmin[2]=xxmin(0); xmin[3]=xxmin(i4); xmin[4]=xxmin(0); xmin[5]=xxmin(0);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else
{
  if (docases) { trialdata d36b(m36b(i4),"ID[5400790175] QITNPEA: cc:4bl: d36b: Marchal, 4blades j=2 quarters, 4-cell bwt, + adjacent 3-cell, small blades"); }
}
  }


 cout << "bmpfactor " << bmpfactor << endl;
}
