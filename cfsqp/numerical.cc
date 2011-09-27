//  Thomas C. Hales.

#include <math.h>
#include "numerical.h"
//#include "morefn.h"

//#include <iomanip.h>
//#include <iostream.h>

// GENERAL STUFF
double pi() { return  4.0*atan(1.0); }
//double pt() { return 0.0553736456684637; }
double adodec() { return -0.581169206221610; }
double bdodec() { return 0.023248513304698; }
//interval yStrongDodec("2.1029244484765344");



/******************* SIMPLEX STUFF ***********************/

double mabs(double a) { return (a>0? a : -a); }
double max(double a,double b) { return (a>b? a : b); }
double real_max(double a,double b) { return max(a,b); }
double min(double a,double b) { return (a<b? a : b); }
double real_pow(double a,double b) { return  pow(a,b);}

double atn2(double x,double y) { return atan2(y,x); } // NB: variable ordering!
double asn(double x) { return asin(x); }


double safesqrt(double t)
	{
	if (t<0.0) return 0.0; else return sqrt(t);
	}

double sqp(double x)
{
  if (x < 0) return 0;
  if (x > 1.0) return sqrt(x);
  return  ((3. / 8.) + (((real_pow((1. - x),3.)) * ((-0.25) + (0.7 * x))) + ((3. * (x / 4.)) - (x * (x / 8.)))));
}

/*
double sql(double x)
{
  return  ( ( x < 1. ) ? -0.025 + 3.15*x - 6.125*real_pow(x,2) + 7.6*real_pow(x,3) - 
	    4.8*real_pow(x,4) + 1.2*real_pow(x,5) : (sqrt(x))) ; 
}
*/

double sqn(double x) {
  if (x <0) return 0;
  if (x >1.0) return sqrt(x);
  return 0.375 + (3.0*x)/4.0 - real_pow(x,2)/8.0 - 
   0.3*real_pow(1.0 - x,3)*real_pow(x,2) + 
    real_pow(1.0 - x,3)*(-0.375 + 1.3*(1 - x)*x) ;
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



double d4(double x1,double x2,double x3,double x4,
	  double x5, double x6) {
  return  -(x2*x3) - x1*x4 + x2*x5 + x3*x6 - x5*x6 +
                        x1*(-x1 + x2 + x3 - x4 + x5 + x6);
}

double dihedral(double x1,double x2,double x3,double x4,
                double x5, double x6)
        {
	  double d = d4(x1,x2,x3,x4,x5,x6);
        return safeacos(d/safesqrt(U(x1,x2,x6)*U(x1,x3,x5)));
        }



double dih_y(double y1,double y2,double y3,double y4,double y5,
        double y6)
        {
        return dihedral(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6);
        }

/*
double upper_dih_y_large(double y1,double y2,double y3,double y4,double y5,
			 double y6) {
  double d= delta_y(y1,y2,y3,y4,y5,y6);
  if (d >1.0) return dih_y (y1,y2,y3,y4,y5,y6);
  double d_4 = d4(y1 * y1,y2*y2,y3 *y3,y4*y4,y5*y5,y6*y6);
  return pi() + 2.0 * y1 * sql(d) * matan( 4.0 * y1 * y1 * d/(d_4 *d_4)) / d_4;
}
*/

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

double tau_m_diff_quotient(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-8;
  return (tau_m(y1+h,y2,y3,y4,y5,y6)-tau_m(y1,y2,y3,y4,y5,y6))/h;
}
double tau_m_diff_quotient2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double h = 1.0e-3;
  return (tau_m(y1+h,y2,y3,y4,y5,y6)-2*tau_m(y1,y2,y3,y4,y5,y6) + tau_m(y1-h,y2,y3,y4,y5,y6))/(h*h);
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

// 2D hexagon perimter problem (sep 21, 2011):

double ell_uvx(double x1,double x2,double x3,double x4,double x5,double x6) {
  double et2 = eta2 (x1,x2,x3);
  return sqrt(et2- (x1/4.0)) + sqrt (et2 - (x2/4.0));
}

// Material added May 19, 2011 for y1 derivatives of tau.

double DUa(double a,double b,double c)
       {
	 return 2.0 *(-a + b + c);
       }

// debug
void show(double y,char* s) {
  //     cout << s << ": " << y << endl;
}

/*
mdtau is a symbolic formula for Sqrt[del] D[taumar,y1].
 */

double mdtau(double y1,double y2,double y3,double y4,double y5,double y6) {
  double x1=y1*y1;
  double x2 = y2*y2;
  double x3 = y3*y3;
  double x4 = y4*y4;
  double x5 = y5*y5;
  double x6 = y6*y6;
  show(x1,"x1"); show(x2,"x2"); show(x3,"x3"); 
   show(x4,"x4"); show(x5,"x5"); show(x6,"x6");

  double chain = 2.0*y1;  // D[x1,y1].
  double Pchain = 2.0;
  double chain2 = 4.0* x1;

  double u135 = U(x1,x3,x5);
  double u126 = U(x1,x2,x6);
  double u234 = U(x2,x3,x4);
  show(u135,"u135"); show(u126,"u126"); show(u234,"u234");

  double uf = 4.0*u135*u126*u234*y1*y2*y3;
  double du135 = DUa(x1,x3,x5);
  double du126 = DUa(x1,x2,x6);

  double Luf = (du135/u135 + du126/u126 )*chain + 1.0/y1;
  show(uf,"uf"); show(du135,"du135"); show(du126,"du126"); show(Luf,"Luf");

  double n4 = x2*x3 + x1*x4 - x2*x5 - x3*x6 + x5*x6 - 
    x1*(-x1 + x2 + x3 - x4 + x5 + x6); // - del4
  double del4 = -n4;

  double n5 = x1*x3 - x1*x4 + x2*x5 - x3*x6 + x4*x6 - 
    x2*(x1 - x2 + x3 + x4 - x5 + x6);  // - del5

  double n6 = x1*x2 - x1*x4 - x2*x5 + x4*x5 - 
    x3*(x1 + x2 - x3 + x4 + x5 - x6) + x3*x6; // - del6

  double Dn4 = 2*x1 - x2 - x3 + 2*x4 - x5 - x6;

  double del = delta_x(x1,x2,x3,x4,x5,x6);

  double del1 = -(x1*x4) + x2*x5 - x3*x5 - x2*x6 + x3*x6 +
   x4*(-x1 + x2 + x3 - x4 + x5 + x6);

  double del2 = x1*x4 - x3*x4 - x2*x5 - x1*x6 + 
    x3*x6 + x5*(x1 - x2 + x3 + x4 - x5 + x6);

  double del3 = x1*x4 - x2*x4 - x1*x5 + x2*x5 - 
    x3*x6 + (x1 + x2 - x3 + x4 + x5 - x6)*x6;

  double Pdel = del1 * chain;

  double Ldel = Pdel/del;
  show(n4,"n4"); show(n5,"n5"); show(n6,"n6");
  show(Dn4,"Dn4"); show(del,"del"); show(del1,"del1"); show(del2,"del2"); 
  show(del3,"del3"); show(Pdel,"Pdel"); show(Ldel,"Ldel");

  double sd4 = 4.0*x1*del;
  double sd5 = 4.0*x2*del;
  double sd6 = 4.0*x3*del;

  double Dsd4 = 4.0*del + 4.0*x1*del1;

  double m4diff = 2.0*Dn4*sd4 - n4* Dsd4;
  double m4 = m4diff*chain*u234*y2*y3;
  double m5 = -4.0*x2*u234*del3*2.0*x1*u135*y3;
  double m6 = -4.0*x3*u234*del2*2.0*x1*u126*y2;

  double const1 = sol_y(2,2,2,2,2,2)/pi();
  double rhoy1 = rho(y1);
  double rhoy2 = rho(y2);
  double rhoy3 = rho(y3);
  double Prhoy1 = c1()/(0.52);

  show(sd4,"sd4"); show(sd5,"sd5"); show(sd6,"sd6");
  show(Dsd4,"Dsd4"); show(m4diff,"m4diff"); show(m4,"m4");
  show (m5,"m5"); show(m6,"m6"); show(const1,"const1"); show(rhoy1,"rhoy1");
  show(rhoy2,"rhoy2"); show(rhoy3,"rhoy3"); show(Prhoy1,"Prhoy1");

  double rr = rhoy1 * m4 + rhoy2 * m5 + rhoy3 * m6;
  
  double term1 = Prhoy1 * pi() * safesqrt(del);
  double t = sqrt(4.0 * x1)/del4;
  double t2 = t*t;
  double term2a = del * t * matan(t2 *del);
  double term2 = term2a * Prhoy1;
  double term3 = rr/uf;

  show(rr,"rr"); show(term1,"term1"); show(t,"t"); show(t2,"t2"); 
  show(term2a,"term2a");
  show(term2,"term2"); show(term3,"term3");

  return term1+term2+term3;
}


/*
mdtau2 =  D[taumar,{y1,2}],
 Most of the code is the same as for mdtau.
 */

double mdtau2(double y1,double y2,double y3,double y4,double y5,double y6) {
  double x1=y1*y1;
  double x2 = y2*y2;
  double x3 = y3*y3;
  double x4 = y4*y4;
  double x5 = y5*y5;
  double x6 = y6*y6;
  show(x1,"x1"); show(x2,"x2"); show(x3,"x3"); 
   show(x4,"x4"); show(x5,"x5"); show(x6,"x6");

  double chain = 2.0*y1;  // D[x1,y1].
  double Pchain = 2.0;
  double chain2 = 4.0* x1;

  double u135 = U(x1,x3,x5);
  double u126 = U(x1,x2,x6);
  double u234 = U(x2,x3,x4);
  show(u135,"u135"); show(u126,"u126"); show(u234,"u234");

  double uf = 4.0*u135*u126*u234*y1*y2*y3;
  double du135 = DUa(x1,x3,x5);
  double du126 = DUa(x1,x2,x6);

  double Luf = (du135/u135 + du126/u126 )*chain + 1.0/y1;
  show(uf,"uf"); show(du135,"du135"); show(du126,"du126"); show(Luf,"Luf");

  double n4 = x2*x3 + x1*x4 - x2*x5 - x3*x6 + x5*x6 - 
    x1*(-x1 + x2 + x3 - x4 + x5 + x6); // - del4
  double del4 = -n4;

  double n5 = x1*x3 - x1*x4 + x2*x5 - x3*x6 + x4*x6 - 
    x2*(x1 - x2 + x3 + x4 - x5 + x6);  // - del5

  double n6 = x1*x2 - x1*x4 - x2*x5 + x4*x5 - 
    x3*(x1 + x2 - x3 + x4 + x5 - x6) + x3*x6; // - del6

  double Dn4 = 2*x1 - x2 - x3 + 2*x4 - x5 - x6;

  double del = delta_x(x1,x2,x3,x4,x5,x6);

  double del1 = -(x1*x4) + x2*x5 - x3*x5 - x2*x6 + x3*x6 +
   x4*(-x1 + x2 + x3 - x4 + x5 + x6);

  double del2 = x1*x4 - x3*x4 - x2*x5 - x1*x6 + 
    x3*x6 + x5*(x1 - x2 + x3 + x4 - x5 + x6);

  double del3 = x1*x4 - x2*x4 - x1*x5 + x2*x5 - 
    x3*x6 + (x1 + x2 - x3 + x4 + x5 - x6)*x6;

  double Pdel = del1 * chain;

  double Ldel = Pdel/del;
  show(n4,"n4"); show(n5,"n5"); show(n6,"n6");
  show(Dn4,"Dn4"); show(del,"del"); show(del1,"del1"); show(del2,"del2"); 
  show(del3,"del3"); show(Pdel,"Pdel"); show(Ldel,"Ldel");

  double sd4 = 4.0*x1*del;
  double sd5 = 4.0*x2*del;
  double sd6 = 4.0*x3*del;

  double Dsd4 = 4.0*del + 4.0*x1*del1;

  double m4diff = 2.0*Dn4*sd4 - n4* Dsd4;
  double m4 = m4diff*chain*u234*y2*y3;
  double m5 = -4.0*x2*u234*del3*2.0*x1*u135*y3;
  double m6 = -4.0*x3*u234*del2*2.0*x1*u126*y2;

  double const1 = sol_y(2,2,2,2,2,2)/pi();
  double rhoy1 = rho(y1);
  double rhoy2 = rho(y2);
  double rhoy3 = rho(y3);
  double Prhoy1 = c1()/(0.52);

  show(sd4,"sd4"); show(sd5,"sd5"); show(sd6,"sd6");
  show(Dsd4,"Dsd4"); show(m4diff,"m4diff"); show(m4,"m4");
  show (m5,"m5"); show(m6,"m6"); show(const1,"const1"); show(rhoy1,"rhoy1");
  show(rhoy2,"rhoy2"); show(rhoy3,"rhoy3"); show(Prhoy1,"Prhoy1");

  double rr = rhoy1 * m4 + rhoy2 * m5 + rhoy3 * m6;
  // no changes in code up to here.

  // start variation in code here.
  double D2n4 = 2.0;
  double D2sd4 = -8*x1*x4 + 8*(-(x1*x4) + x2*x5 - x3*x5 - x2*x6 + x3*x6 + 
			       x4*(-x1 + x2 + x3 - x4 + x5 + x6));
  double Dm4diff = 2.0 * D2n4 * sd4 + Dn4 * Dsd4 - n4 *D2sd4;
  double Pm4 = (Dm4diff * chain2 + m4diff * Pchain ) * u234 * y2 * y3;
  double Ddel3 = x4 - x5 + x6;
  double Ddel2 = x4 + x5 - x6;
  double Pm5 =  (Ddel3 * x1 * u135 + del3 * 1.0 * u135 + del3 * x1 * du135) * 
    chain * (-4.0 * x2 * u234 * 2.0 * y3);
  double Pm6 = (Ddel2 * x1 * u126 + del2 * 1.0 * u126 + del2 * x1 * du126) *
    chain * (-4.0 * x3 * u234 * 2.0 * y2);

  double PrrC = 2.0 * Prhoy1 * m4 + rhoy1 * Pm4 + rhoy2 * Pm5 + rhoy3 * Pm6;
  double P2tauNum = (PrrC) + (-Luf - 0.5 * Ldel) * rr;
  double P2tau = P2tauNum/ (uf * safesqrt(del));

  show(Pm4,"Pm4"); show(Pm5,"Pm5"); show(Pm6,"Pm6"); show(PrrC,"Prrc");
  show(P2tauNum,"P2taunum"); show(P2tau,"P2tau");

  return P2tau;
}
