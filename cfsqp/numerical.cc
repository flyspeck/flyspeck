//  Thomas C. Hales.

#include <math.h>
#include "numerical.h"
//#include "morefn.h"

// GENERAL STUFF
double pi() { return  4.0*atan(1.0); }
//double pt() { return 0.0553736456684637; }
double adodec() { return -0.581169206221610; }
double bdodec() { return 0.023248513304698; }
//interval yStrongDodec("2.1029244484765344");



/******************* SIMPLEX STUFF ***********************/

double mabs(double a) { return (a>0? a : -a); }
double max(double a,double b) { return (a>b? a : b); }
double min(double a,double b) { return (a<b? a : b); }
double real_pow(double a,double b) { return  pow(a,b);}

double atn2(double x,double y) { return atan2(y,x); } // NB: variable ordering!
double asn(double x) { return asin(x); }


double safesqrt(double t)
	{
	if (t<0.0) return 0.0; else return sqrt(t);
	}

double pos(double t)
	{
	return (t>0.0 ? t : 0.0);
	}

double safeacos(double t)
	{
	  if (t<-1.0) return pi();
	if (t>1.0) return 0.0;
	return acos(t);
	}

double matan(double t) 
{
  double r = sqrt(mabs(t));
  if (t > 1.0e-8) return (atn2(1.0,r) / r);
  if (t < -1.0e-8) return ( (0.5 / r) * (log ((1.0 + r)/(1.0-r))) );
  return 1.0 - t / 3.0 + t*t / 5.0 - t*t*t / 7.0;
}

double delta_x(double x1,double x2,double x3,double x4,double x5,double x6)
        {
        return (-x1+x2+x3-x4+x5+x6)*(x1*x4) +
                (x1-x2+x3+x4-x5+x6)*(x2*x5)+
                (x1+x2-x3+x4+x5-x6)*(x3*x6) -
                (x2*x3*x4 +x1*x3*x5+x1*x2*x6+x4*x5*x6);
        }

double delta_y(double y1,double y2,double y3,double y4,double y5,double y6)
        {
	  double x[6]={y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6};
	  return delta_x(x[0],x[1],x[2],x[3],x[4],x[5]);
        }


double U(double a,double b,double c)
       {
        return -a*a-b*b-c*c+2.0*(a*b+b*c+c*a);
       }

double dihedral(double x1,double x2,double x3,double x4,
                double x5, double x6)
        {
        double d4 = -(x2*x3) - x1*x4 + x2*x5 + x3*x6 - x5*x6 +
                        x1*(-x1 + x2 + x3 - x4 + x5 + x6);
        return safeacos(d4/safesqrt(U(x1,x2,x6)*U(x1,x3,x5)));
        }

double dih_y(double y1,double y2,double y3,double y4,double y5,
        double y6)
        {
        return dihedral(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6);
        }

double dih2_y(double y1,double y2,double y3,double y4,double y5,
        double y6)
        {
	  return dih_y(y2,y3,y1,y5,y6,y4);
        }

double dih3_y(double y1,double y2,double y3,double y4,double y5,
        double y6)
        {
	  return dih_y(y3,y1,y2,y6,y4,y5);
        }


double dihR(double a,double b,double c)
	{
	static const double pi2 = 1.57079632679489661923132169164;
	if (a>=b) return pi2;
	if (b>=c) return 0.0;
	return dihedral(a*a,b*b,c*c,c*c-b*b,c*c-a*a,
			b*b-a*a);
	}


double AA(double y1,double y2,double y3,double y4,double y5,double y6)
        {
        return y1*y2*y3 + (y1*(y2*y2+y3*y3-y4*y4)+
                          y2*(y1*y1+y3*y3-y5*y5)+
                          y3*(y1*y1+y2*y2-y6*y6))/2.0;
        }

double presolid(      double y1,double y2,double y3,
                        double y4,double y5,double y6)
        {
        double a = AA(y1,y2,y3,y4,y5,y6);
        return delta_x(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6)/(a*a);
        }

double sol_y(double y1,double y2,double y3,double y4,double y5,double y6)
        {
	  return dih_y(y1,y2,y3,y4,y5,y6) + dih2_y(y1,y2,y3,y4,y5,y6)
	    +dih3_y(y1,y2,y3,y4,y5,y6) - pi(); 
           // corrected 2010-6-12.
	  //  old formula: 2.0*atan(safesqrt(presolid(y1,y2,y3,y4,y5,y6))/2.0);
          // old formula incorrect for sol_y(2, 2, 2, 2.52, 3.91404, 3.464);
        }

double solR(double a,double b,double c)
	{
	if (a>=b) return 0.0;
	if (b>=c) return 0.0;
	return sol_y(a,b,c,safesqrt(c*c-b*b),safesqrt(c*c-a*a),
		safesqrt(b*b-a*a));
	}

const double doct = 0.72090294951746509284124483502;
double gamma(double y1,double y2,double y3,double y4,
                        double y5, double y6)
        {
        double x1=y1*y1, x2 = y2*y2, x3=y3*y3, x4=y4*y4, x5=y5*y5, x6=y6*y6;
        double t = safesqrt(delta_x(x1,x2,x3,x4,x5,x6))/2.0;
        double a1,a2,a3,a4;
        a1 = AA(y1,y2,y3,y4,y5,y6);
        a2 = AA(y1,y5,y6,y4,y2,y3);
        a3 = AA(y4,y5,y3,y1,y2,y6);
        a4 = AA(y4,y2,y6,y1,y5,y3);
        return -doct*t/6.0 + (2.0/3.0)*(atan(t/a1)+atan(t/a2)+
                                          atan(t/a3)+atan(t/a4));
        };


double eta2(double x1,double x2,double x3)
        {
        return x1*x2*x3/U(x1,x2,x3);
        }

double radf(double y1,double y2,double y3)
        {
        return safesqrt(eta2(y1*y1,y2*y2,y3*y3));
        }

double eta0(double h)
{
  return radf(2.0* h, 2.0,2.51);
}

double chi(   double x1,double x2,double x3,
                double x4,double x5,double x6)
        {
        return x3*x6*(x4+x5-x6) + x2*x5*(x4-x5+x6)+x1*x4*(-x4+x5+x6)
               -2.0*x4*x5*x6;
        }

double rad(double x1,double x2,double x3,double x4,
                double x5,double x6)
        {
        double c = chi(x1,x2,x3,x4,x5,x6);
        return safesqrt(eta2(x4,x5,x6)+
                        c*c/(4.0*U(x4,x5,x6)*delta_x(x1,x2,x3,x4,x5,x6)));
        }

double rady(double y1,double y2,double y3,double y4,double y5,double y6)
	{
	return rad(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6);
	}

double arc(double y1,double y2,double y6)
    {
    return acos( (y1*y1+y2*y2-y6*y6)/(2.*y1*y2));
    }

double circum2(double x1,double x2,double x3,double x4,
                double x5,double x6)
        {
        double c = chi(x1,x2,x3,x4,x5,x6);
        return (eta2(x4,x5,x6)+
                        c*c/(4.0*U(x4,x5,x6)*delta_x(x1,x2,x3,x4,x5,x6)));
        };


/*
double volR(double a,double b, double c) 
{
  return a*safesqrt(b*b-a*a)*safesqrt(c*c-b*b)/6.0 ;
}
*/

//---- stuff for quad clusters.

double solid9(double y[9])
	{
	return sol_y(y[0],y[1],y[2],y[3],y[4],y[5])+
		sol_y(y[6],y[1],y[2],y[3],y[7],y[8]);
	}

double dih9_0(double y[9])
	{
	return dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}

double dih9_2(double y[9])
	{
	return dih_y(y[2],y[0],y[1],y[5],y[3],y[4])+
		dih_y(y[2],y[6],y[1],y[8],y[3],y[7]);
	}

double dih9_1(double y[9])
	{
	return dih_y(y[1],y[0],y[2],y[4],y[3],y[5])+
		dih_y(y[1],y[6],y[2],y[7],y[3],y[8]);
	}

double dih9_6(double y[9])
	{
	return dih_y(y[6],y[1],y[2],y[3],y[7],y[8]);
	}

double crossdiag(double y[9])
	{
	double    x3=y[3]*y[3], 
		x4=y[4]*y[4], x5=y[5]*y[5], 
		x7=y[7]*y[7], x8=y[8]*y[8];
	double dd = dih_y(y[3],y[1],y[5],y[0],y[4],y[2])+
			dih_y(y[3],y[1],y[8],y[6],y[7],y[2]);
	//	static double pi = 3.14159265358979323;
	double c0;
	double c1 = -x3*x3-x5*x8-x4*x7+x3*(x5+x8+x4+x7)+x5*x7+x4*x8;
	if (dd>pi())
		{
		  c0 = cos(2.0*pi()-dd)*sqrt(U(x3,x5,x4)*(U(x3,x8,x7)));
		return sqrt((c0-c1)/(-2.0*x3));
		}
	else
		{
		c0 = cos(dd)*sqrt(U(x3,x5,x4)*(U(x3,x8,x7)));
		return  sqrt((c0-c1)/(-2.0*x3));
		}
	}


// Flyspeck functions:

double interp(double x1,double y1,double x2,double y2,double x) {
  return y1 + (x - x1) *(y2-y1)/(x2-x1);
}

double hminus() { return 1.2317544220903216;  }

double h0() { return 1.26; }

double lfun(double h) {
  return interp(  1.0,1.0,    h0(),0.0,  h);
}

double lmfun(double h) {
  return max(0,lfun(h));
}

double c1() { return sol_y(2,2,2,2,2,2)/pi(); } // delta0/Pi

// lfun[y/2]
double ly(double y) {
  return interp(2.0,1.0,    2.52,0.0, y);
}

double rho(double y) {
  return (1+c1()) - c1()*ly(y);
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

double tau_m_alt(double y1,double y2,double y3,double y4,double y5,double y6) {
  return sol_y(y1,y2,y3,y4,y5,y6)*(1.0 + c1()) - 
    c1()*(lnazim(y1,y2,y3,y4,y5,y6)+lnazim(y2,y3,y1,y5,y6,y4)+lnazim(y3,y1,y2,y6,y4,y5));
}

double tau_m(double y1,double y2,double y3,double y4,double y5,double y6) {
  return rho(y1)*dih_y(y1,y2,y3,y4,y5,y6)+rho(y2)*dih_y(y2,y3,y1,y5,y6,y4)+
    rho(y3)*dih_y(y3,y1,y2,y6,y4,y5) - (pi() + sol_y(2,2,2,2,2,2));
}

double hplus =  1.3254; 


int critical_edge_y(double t) {
  return ((t >= 2.0*hminus()) && (t <= 2.0*hplus));
}

int wtcount6_y(double y1,double y2,double y3,double y4,double y5,double y6) {
  int count =0;
  if (critical_edge_y(y1)) { count++; }
  if (critical_edge_y(y2)) { count++; }
  if (critical_edge_y(y3)) { count++; }
  if (critical_edge_y(y4)) { count++; }
  if (critical_edge_y(y5)) { count++; }
  if (critical_edge_y(y6)) { count++; }
  return count;
}

int wtcount3_y(double y1,double y2,double y3) {
  int count =0;
  if (critical_edge_y(y1)) { count++; }
  if (critical_edge_y(y2)) { count++; }
  if (critical_edge_y(y3)) { count++; }
  return count;
}

double bump(double r) { 
  double bmpfactor = 0.005;
  double s = (r-h0())/(hplus-h0());
  return bmpfactor *(1.0 - s*s);
}

double bmp2(double y1,double y4) {
  return (bump(y1/2.0) - bump(y4/2.0));
} 

double beta_bump_y(double y1,double y2,double y3,double y4,double y5,double y6) {
  if (2!=wtcount6_y(y1,y2,y3,y4,y5,y6))  { return 0.0; }
  if (!critical_edge_y(y1))  { return 0.0; }
  if (!critical_edge_y(y4))  { return 0.0; }
  return bmp2(y1,y4);
}

double machine_eps() { return 2.0e-8; } // is 0 in formal text.
