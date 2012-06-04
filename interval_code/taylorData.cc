/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                     */
/* ========================================================================== */

// parameter passing modes (const-reference parameters)
// http://pages.cs.wisc.edu/~hasti/cs368/CppTutorial/NOTES/PARAMS.html


#include <iomanip>
#include <utility>
#include <tr1/unordered_map>
extern "C"
{
#include <math.h>
#include <time.h>
#include <stdlib.h>
#include <float.h>
#include <assert.h>
}
#include "interval.h"
#include "univariate.h"
#include "lineInterval.h"
#include "wide.h"
#include "secondDerive.h"
#include "taylorData.h"

using namespace std;
using namespace tr1;


/* ========================================================================== */
/*                                                                            */
/*   Section:basics                                                      */
/*                                                                            */
/* ========================================================================== */

 
static inline double max(double x,double y)
{ return (x>y ? x : y); }

static inline double dabs(const interval x) {
  return interMath::sup(interMath::max(x,-x));
}

static void intervalToAbsDouble(const interval DDx[6][6],double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 	
			  DD[i][j]= dabs(DDx[i][j]);
}

static lineInterval plus (const lineInterval& f, const lineInterval& g)  {
  lineInterval h;
  h.f = f.f + g.f;
  for (int i=0;i<6;i++) {
    h.Df[i] = f.Df[i] + g.Df[i];
  }
  return h;
}

static void testAbs(double DD[6][6],const char* s) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD[i][j] < 0) {
	error::message("negative absolute value detected " );
	cout << s << " " << DD[i][j] << " " << i << " " << j << endl;
      }
    }
}



/* ========================================================================== */
/*                                                                            */
/*   Section:taylorData                                                           */
/*                                                                            */
/* ========================================================================== */



taylorData::taylorData(domain w0) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j]=0.0; }
  w = w0;
}

taylorData::taylorData(const lineInterval& h0,
			       const domain& w0,const double DD0[6][6])
{
  w = w0;
  for (int i=0;i<6;i++) {
    if (w.getValue(i) < 0.0) { error::message("constructing neg width ");
      cout << w.getValue(i) << " " << (w0.getValue(i)-w.getValue(i)) << " " << i << endl;
    }
  }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD0[i][j] < 0.0) { error::message("invalid DD input"); 
	cout << i << " " << j << " " << DD0[i][j] << endl;
      }
    }
  tangentVector = h0;
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=DD0[i][j];
}

lineInterval taylorData::tangentVectorOf() const
{
  return tangentVector;
}

static double taylorError(const domain& w,const double DD[6][6])
{
  interMath::up();
  double t=0.0;
  int i,j;
  for (i=0;i<6;i++) {
    if (w.getValue(i) < 0.0) { 
      error::message("negative width"); cout << w.getValue(i); }
  }
  for (i=0;i<6;i++) for (j=0;j<6;j++) {
      if (DD[i][j] < 0.0)  { error::message("negative DD in taylorError"); } 
    }
  for (i=0;i<6;i++) t = t + (w.getValue(i)*w.getValue(i))*DD[i][i];
  t = t/2.0;
  for (i=0;i<6;i++) for (j=i+1;j<6;j++)
		      t = t+ (w.getValue(i)*w.getValue(j))*DD[i][j];
  return t;
}

double taylorData::upperBound() const {
  double err = taylorError(w,DD);
  interMath::up();
  double t = tangentVector.hi() + err;
  for (int i=0;i<6;i++) t = t+ w.getValue(i)*dabs(tangentVector.partial(i));
  return t;
}

double taylorData::lowerBound() const {
  double err = taylorError(w,DD);
  interMath::down();
  double t = tangentVector.low() - err;
  for (int i=0;i<6;i++) t = t + (-w.getValue(i))*dabs(tangentVector.partial(i));
  return t;
}

double taylorData::upperboundQ 
(const taylorData& cA,const taylorData& cB) {
  interMath::up();
  double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
  double t = cA.tangentVector.hi()+cB.tangentVector.hi() + err;
  int k[3]={0,4,5},i;
  for (i=0;i<3;i++) t = 
		      t+ cA.w.getValue(k[i])*dabs(cA.tangentVectorOf().partial(k[i]));
  for (i=0;i<3;i++) t = 
		      t+ cB.w.getValue(k[i])*dabs(cB.tangentVectorOf().partial(k[i]));
  for (i=1;i<4;i++) t = t+ cB.w.getValue(i)*
		      dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
  return t;
}

double taylorData::lowerboundQ
(const taylorData& cA,const taylorData& cB)
{
  interMath::up();
  double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
  interMath::down();
  double t = cA.tangentVector.low()+cB.tangentVector.low() - err;
  int k[3]={0,4,5},i;
  for (i=0;i<3;i++) t = t+ 
		      (-cA.w.getValue(k[i]))*dabs(cA.tangentVectorOf().partial(k[i]));
  for (i=0;i<3;i++) t = t+ 
		      (-cB.w.getValue(k[i]))*dabs(cB.tangentVectorOf().partial(k[i]));
  for (i=1;i<4;i++) t = t+ (-cB.w.getValue(i))
		      *dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
  return t;
}


double taylorData::upperPartial(int i) const
{
  if ((i<0)||(i>=6)) 
    { error::message("upperPartial index out of range"); return 0; }
  interMath::up();
  double err = 0.0;
  for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
  return interMath::sup(tangentVector.partial(i)) + err;
}

double taylorData::lowerPartial(int i) const
{
  if ((i<0)||(i>=6)) 
    { error::message("upperPartial index out of range"); return 0; }
  interMath::up();
  double err = 0.0;
  for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
  interMath::down();
  return interMath::inf(tangentVector.partial(i)) - err;
}

taylorData taylorData::plus
(const taylorData& t1,const taylorData& t2)
{
  double DD[6][6];
  int i,j;
  interMath::up();
  for (i=0;i<6;i++) for (j=0;j<6;j++) 
		      DD[i][j]= t1.DD[i][j]+t2.DD[i][j];
  lineInterval s;
  s.f = t1.tangentVector.f + t2.tangentVector.f;
  for (i=0;i<6;i++) s.Df[i]= t1.tangentVector.Df[i]+ t2.tangentVector.Df[i];
  for (i=0;i<6;i++) if (t1.w.getValue(i)!=t2.w.getValue(i)) 
		      error::message("bad domain in ti");
  taylorData t(s,t1.w,DD);
  return t;
}

taylorData taylorData::scale
(const taylorData& t1,const interval& c)
{
  double absC = dabs(c); 
  double DD[6][6];
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
			  { DD[i][j]= t1.DD[i][j]*absC; }
  lineInterval s = t1.tangentVector;
  s.f = s.f *c;
  for (int i=0;i<6;i++) s.Df[i]=s.Df[i]*c;
  taylorData t(s,t1.w,DD);
  return t;
}

		

/* ========================================================================== */
/*                                                                            */
/*   Section:primitiveLC                                                               */
/*                                                                            */
/* ========================================================================== */

// Locally constant constructor.  All derivative information is zero.

class primitiveLC : public primitive 
{
private:
  interval (*hfn)(const domain&,const domain&);
  
public:
  lineInterval tangentAtEstimate(const domain& x) const { return (*hfn)(x,x); }
  taylorData evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  primitiveLC(interval (*)(const domain&,const domain& ));
};


taylorData primitiveLC::evalf4
(const domain& w,const domain& x,const domain& y,const domain& z) const
{
  double DD[6][6];
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  lineInterval t( (*hfn)(x,z) );
  return taylorData(t,w,DD);
}

primitiveLC::primitiveLC(interval (*hfn0)(const domain&,const domain&))
{
  hfn = hfn0;
}

Function Function::mk_LC(interval (*hfn0)(const domain&,const domain&)) {
  primitiveLC* t = new primitiveLC(hfn0);
  Function f(t);
  return f;
}

/* ========================================================================== */
/*                                                                            */
/*   Section:primitiveA                                                               */
/*                                                                            */
/* ========================================================================== */


class primitiveA : public primitive 
{
private:
  lineInterval (*hfn)(const domain&);
  
  // all the arrays of double [6][6] are bounds on abs value of second partials.
  int (*setAbsSecond)(const domain& x,const domain& z,double [6][6]);
  
public:
  lineInterval tangentAtEstimate(const domain& x) const { return (*hfn)(x); }
  taylorData evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  primitiveA(lineInterval (*)(const domain& ),
	     int (*)(const domain& ,const domain&,double [6][6]));
};




taylorData primitiveA::evalf4
(const domain& w,const domain& x,const domain& y,const domain& z) const
{
  double DD[6][6];
  (*setAbsSecond)(x,z,DD);
  lineInterval tangentVector = (*hfn)(y);
  return taylorData(tangentVector,w,DD);
}

primitiveA::primitiveA(lineInterval (*hfn0)(const domain&),
		       int (*setAbsSecond0)(const domain&,const domain&,double [6][6]))
{
  hfn = hfn0;
  setAbsSecond = setAbsSecond0;
}

Function Function::mk_raw(lineInterval (*hfn0)(const domain& ),
	 int (*setAbsSecond0)(const domain& ,const domain&,double [6][6])) {
  primitiveA* t = new primitiveA(hfn0,setAbsSecond0);
  Function f(t);
  return f;
};



/* ========================================================================== */
/*                                                                            */
/*   Section:primitive_monom                                                               */
/*                                                                            */
/* ========================================================================== */


// procedures for monomial terms x1^n1 ... x6^n6 .

/*
interval mpow_i(const interval& x,int n) {
  static const interval one("1");
  static const interval zero("0");
  switch (n) {
  case 0 : return one;
  case 1 : return x;
  default : 
    if (n <0) { error::fatal("negative exponent in mpow_i");  return zero; } else
      {
	int m = n / 2;
	interval u = mpow_i(x,m);
	interval u2 = u*u;
	return ( n % 2 ? x * u2 : u2);
      }
  }
}
*/

interval mpow_i(const interval& x,int n) {
  static const interval one("1");
  static const interval zero("0");
  switch (n) {
  case 0 : return one;
  case 1 : return x;
  default : 
    if (n <0) { error::fatal("negative exponent in mpow_i");  return zero; } 
    if (interMath::inf(x) < 0.0) { error::fatal("negative base in mpow"); return zero; }
    interMath::up();
    double u = pow(interMath::sup(x),n);
    interMath::down();
    double l = pow(interMath::inf(x),n);
    interval lu(l,u);
    return lu;
  }
}

// compute x^n, n x^{n-1},

void mpow_d(const interval& x, int n, interval x_d[2]) {
  static const interval zero("0");
  static const interval one("1");
  switch (n) {
  case 0: x_d[0] = one; x_d[1]=zero; return;
  case 1: x_d[0] = x; x_d[1]=one; return;
   default: 
     if ((n < 0) || (n > 50)) { error::fatal(" exponent out of range in mpow_d"); return; } 
     interval u = mpow_i(x,n-1);
     interval ni(1.0* n,1.0* n); // N.B. for huge n, this can produce a rounding error.
     x_d[0] = x * u; x_d[1] = ni * u;
     return;
  }
}

// compute x^n, n x^{n-1}, n (n-1) x^{n-2}:

void mpow_d_dd(const interval& x, int n, interval x_d_dd[3]) {
  static const interval zero("0");
  static const interval one("1");
  static const interval two("2");
  for (int i =0;i<3;i++) { x_d_dd[i]=zero; }
  switch (n) {
  case 0: x_d_dd[0] = one; return;
  case 1: x_d_dd[0] = x; x_d_dd[1]=one; return;
  case 2: x_d_dd[0] = x*x; x_d_dd[1]=two * x; x_d_dd[2] = two; return;
  default: 
    if ((n < 0) || (n > 50)) { error::fatal("exponent range in mpow_d_dd"); return; } 
    interval u = mpow_i(x,n-2);
    interval ni(1.0* n,1.0* n); // N.B. for huge n, this can produce a rounding error.
    interval mi(n-1.0,n-1.0);
    interval xu = x * u;
    x_d_dd[0] = x * xu;  x_d_dd[1] = ni * xu;  x_d_dd[2]= ni * mi * u;
    return;
  }
}

// 
static const lineInterval tangent_of_monom(const domain& w,const int n[6]) {
  static const interval one("1");
  lineInterval t;
  t.f = one;
  for (int j=0;j<6;j++) { t.Df[j] = one; };
  for (int i=0;i<6;i++) {
    double w0 = w.getValue(i);
    interval x(w0,w0);
    interval y[2];
    mpow_d(x,n[i],y);
    t.f = t.f * y[0];
    for (int j=0;j<6;j++)  { t.Df[j] = t.Df[j] * (i==j ? y[1] : y[0]);    }
  }
  return t;
}

static const taylorData taylor_of_monom(const domain& w,const domain& x,
					    const domain& y,const domain& z,const int n[6]) {
  static const interval one("1");
  static const interval zero("0");
  interval DDw[6][6];
  
  // initialize
  int nz = 0;
  int p[6];
  for (int i=0;i<6;i++) if (n[i]>0) { p[nz] = i; nz ++; }
  for (int j=0;j<6;j++) for (int k=0;k<6;k++) { DDw[j][k]=zero; }
  for (int j=0;j<nz;j++) for (int k=0;k<nz;k++) { DDw[p[j]][p[k]]=one; }
  interval r[6][3];
  for (int i=0;i<6;i++) { 
    interval xz(x.getValue(i),z.getValue(i));
    mpow_d_dd(xz,n[i],r[i]); 
  }
  // calculate second derivatives
  for (int j=0;j<nz;j++) for (int k=0;k<nz;k++) for (int i=0;i<nz;i++) {
	if ((i!=j) && (i != k)) { DDw[p[j]][p[k]] = DDw[p[j]][p[k]] * r[p[i]][0]; }
      }
  for (int i=0;i<nz;i++) { DDw[p[i]][p[i]] = DDw[p[i]][p[i]] * r[p[i]][2]; }
  for (int j=0;j<nz;j++) 
    for (int k=0;k<nz;k++) 
      if (j!=k) {
	DDw[p[j]][p[k]] = DDw[p[j]][p[k]] * (r[p[j]][1] * r[p[k]][1]);
      }
  double DD[6][6];
  intervalToAbsDouble(DDw,DD);
  lineInterval tangentVector = tangent_of_monom(y,n);
  return taylorData(tangentVector,w,DD);
}

class primitive_monom : public primitive 
{
private:
  int n[6];
  
public:
  lineInterval tangentAtEstimate(const domain& x) const { return tangent_of_monom(x,n); }
  taylorData evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const {
    return taylor_of_monom(w,x,y,z,n);
  }
  primitive_monom(const int [6]);
};

primitive_monom::primitive_monom(const int m[6])
{
  for (int i=0;i<6;i++) { n[i] = m[i]; }
}

Function Function::mk_monomial(const int m[6]) {
  primitive_monom* t = new primitive_monom(m);
  Function f(t);
  return f;
};

/* implement monomial */
Function Function::mk_monomial(int i1,int i2,int i3,int i4,int i5,int i6) {
  int m[6]={i1,i2,i3,i4,i5,i6};
  //primitive* pp = new primitive_monom(n); // minor memory leak
  //Function g(pp);
  //return g;
  primitive_monom* t = new primitive_monom(m);
  Function f(t);
  return f;
}




/* ========================================================================== */
/*                                                                            */
/*   Section:primitive_univariate                                                     */
/*                                                                            */
/* ========================================================================== */


class primitive_univariate : public primitive 
{
private:
  int slot;
  const univariate* f;
  
public:
  
  lineInterval tangentAtEstimate(const domain& x) const ;
  
  taylorData evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  
  primitive_univariate(const univariate&x, int slot0 ) { f = &x; slot = slot0; };
};

/*
Function(const univariate&x, int slot0) {
  primitive_univariate t(x,slot0);
  return t;
}
*/

lineInterval primitive_univariate::tangentAtEstimate(const domain& x) const {
  static interval zero("0");
  lineInterval a;
  double y = x.getValue(slot);
  interval t(y,y);
  a.f = f->eval(t,0);
  for (int i=1;i<6;i++) a.Df[i]=zero;
  a.Df[slot] = f->eval(t,1);
  return a;
}

taylorData primitive_univariate::evalf4(const domain& w,const domain& x,
					    const domain& y,const domain& z) const {
  double DD[6][6];
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j]=0.0; }
  interval t(x.getValue(slot),z.getValue(slot));
  DD[slot][slot] = dabs(f->eval(t,2));
  taylorData a(primitive_univariate::tangentAtEstimate(y),w,DD);
  return a;
}

/* ========================================================================== */
/*                                                                            */
/*   Section:primitiveC  composites                                                   */
/*                                                                            */
/* ========================================================================== */


class primitiveC : public primitive 
{
private:
  const Function* hdr;
  const Function* p1;
  const Function* p2;
  const Function* p3;
  const Function* p4;
  const Function* p5;
  const Function* p6;
  
public:
  
  lineInterval tangentAtEstimate(const domain& x) const ;
  
  taylorData evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  
  primitiveC(const Function* ,
	     const Function*,const Function*,const Function*,
	     const Function*,const Function*,const Function*
	     );
};

primitiveC::primitiveC
  (const Function* hdr0, 
   const Function* p10,const Function* p20,const Function* p30,
   const Function* p40,const Function* p50,const Function* p60) 
{
  hdr = hdr0;
  p1 = p10;
  p2  =p20;
  p3 = p30;
  p4 = p40;
  p5 = p50;
  p6 = p60;
};

lineInterval primitiveC::tangentAtEstimate(const domain& x) const
{
  if (!hdr) { error::fatal ("tangentAtEstimate: function expected, returning 0");   }
  lineInterval pv[6];
  pv[0] = p1->tangentAtEstimate(x);
  pv[1] = p2->tangentAtEstimate(x);
  pv[2] = p3->tangentAtEstimate(x);
  pv[3] = p4->tangentAtEstimate(x);
  pv[4] = p5->tangentAtEstimate(x);
  pv[5] = p6->tangentAtEstimate(x);
  // calculate narrow value range of pv[i].
  double a[6], b[6];
  for (int i=0;i<6;i++) {
    a[i]=interMath::inf(pv[i].f); b[i] =interMath::sup(pv[i].f);
  }
  domain aN(a);
  domain bN(b);
  // 
  // value of outer function
  taylorData fN = hdr->evalf(aN,bN);
  // derivatives of outer function
  interval fN_partial[6]; // narrow partials (at interval image of a point)
  interval pN_partial[6][6];  // function i, partial j.
  for (int i=0;i<6;i++) {
    interval tN(fN.lowerPartial(i),fN.upperPartial(i));
    fN_partial[i] = tN;
    for (int j=0;j<6;j++) {
      pN_partial[i][j] = pv[i].Df[j];
    }
  }
  // apply chain rule to compute narrow first derivative data.
  interval cN_partial[6];
  static interval zero("0");
  for (int i=0;i<6;i++) {
    cN_partial[i] = zero;
    for (int j=0;j<6;j++) { cN_partial[i]  =cN_partial[i] + fN_partial[j] * pN_partial[j][i]; }
  }
  lineInterval lin;
  lin.f = fN.tangentVectorOf().f;
  for (int i=0;i<6;i++) {
    lin.Df[i] = cN_partial[i];
  }
  return lin;
};

taylorData primitiveC::evalf4(const domain& w,const domain& x,const domain& y,const domain& z ) const
{
  if (!hdr) { error::fatal ("evalf4: function expected, returning 0");   }
  
  taylorData pv[6] = {
    p1->evalf4(w,x,y,z),
    p2->evalf4(w,x,y,z),
    p3->evalf4(w,x,y,z),
    p4->evalf4(w,x,y,z),
    p5->evalf4(w,x,y,z),
    p6->evalf4(w,x,y,z)};
  
  // calculate wide value range of pv[i], 
  double aw[6], bw[6];
  for (int i =0;i<6;i++) {
    aw[i] = pv[i].lowerBound(); bw[i] = pv[i].upperBound(); 
  }

  // calculate narrow value range of pv[i].
  double a[6],b[6];
  for (int i=0;i<6;i++) {
    a[i]=pv[i].tangentVectorOf().low(); b[i] =pv[i].tangentVectorOf().hi();
  }
  
  // choose an expansion point u near p(y), and widths wu for image of p1,...,p6 under y
  double u[6],wu[6],wf[6];
  interMath::up();
  for (int i=0;i<6;i++) {
    u[i] =(b[i] + a[i] )/2.0;
    wf[i] = max(b[i]-u[i],u[i]-a[i]);  // narrow w
    wu[i] = max(bw[i]-u[i],u[i]-aw[i]); // wide w.
  }
  taylorData fu = hdr->evalf4(wu,aw,u,bw);

  // now compute interval tangentVector of f (at exact point p(y) as opposed to approximation u)
  lineInterval fpy;
  {
    taylorData t(fu.tangentVectorOf(),wf,fu.DD); // narrow adjustment from p(y) to u.
    interval v(t.lowerBound(),t.upperBound());
    fpy.f = v;
    for (int i=0;i<6;i++)  {
      interval r(t.lowerPartial(i),t.upperPartial(i));
      fpy.Df[i] = r;
    }
  }

  // apply chain rule to compute narrow first derivative data.
  lineInterval lin;  {
    lin.f = fpy.f;
  static interval zero("0");
  for (int i=0;i<6;i++)     lin.Df[i] = zero; 
  for (int j=0;j<6;j++) {
    if ((fpy.Df[j].zero())) continue;
    for (int i=0;i<6;i++)
      {
	interval r = pv[j].tangentVectorOf().partial(i);
	if (!(r.zero()))
	  lin.Df[i]  = lin.Df[i] + fpy.Df[j] * r;
      }
  }}

  // initialize second derivative data.
  double fW_partial_dabs[6]; // abs value of wide partials (over entire domain)
  double pW_partial_dabs[6][6]; // abs of function p i, partial j.
  for (int i=0;i<6;i++) {
    interval tW(fu.lowerPartial(i),fu.upperPartial(i));
    fW_partial_dabs[i] = dabs( tW);
    for (int j=0;j<6;j++) {
      interval uW(pv[i].lowerPartial(j),pv[i].upperPartial(j));
      pW_partial_dabs[i][j] = dabs(uW);
    }
  }

  // apply chain rule to compute bound on second derivative data. 
  // This is the "wide" part of the calc.
  // Often, many terms in the 4-nested loop are zero.
  double DcW[6][6];
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DcW[i][j]= 0.0; }
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      for (int k=0;k<6;k++) {
	if (pv[k].DD[i][j] != 0.0) 
	  DcW[i][j] = DcW[i][j] +  fW_partial_dabs[k] * pv[k].DD[i][j];
      }}
  int Nki = 0;
  int Nmj = 0;
  int kk[36], ii[36], jj[36], mm[36];
  double rki[36], rmj[36];
  for (int i=0;i<6;i++) for (int k=0;k<6;k++) {
      if (!(0.0==pW_partial_dabs[k][i])) {
      rki[Nki] = pW_partial_dabs[k][i]; kk[Nki]= k; ii[Nki]= i; Nki++;
      if (Nki > 36) { error::fatal("Nki out of range "); }
      }}
  for (int j=0;j<6;j++)  for (int m=0;m<6;m++) {
      if (!(0.0==pW_partial_dabs[m][j])) {
      rmj[Nmj] = pW_partial_dabs[m][j]; mm[Nmj]= m; jj[Nmj]= j; Nmj++;
      if (Nmj > 36) { error::fatal("Nmj out of range "); }
      }}
  interMath::up();
  for (int ki=0;ki<Nki;ki++) 
    for (int mj=0;mj<Nmj;mj++) 
      { DcW[ii[ki]][jj[mj]] = DcW[ii[ki]][jj[mj]] + fu.DD[kk[ki]][mm[mj]] * rki[ki] * rmj[mj];    }

  // debug: 
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (fu.DD[i][j]<0.0) { cout << endl << i << " " << j << " " << fu.DD[i][j] << endl;
	error::fatal("DD neg fu.DD in primitive C"); }
    }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) for (int k=0;k<6;k++) { 
	if (pv[k].DD[i][j]<0.0) { cout << endl << i << " " << j << " " << k << " " << pv[k].DD[i][j]  << endl;
	error::fatal("DD neg pv[].DD in primitive C"); }
    }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DcW[i][j]<0.0) { cout << endl<<  i << " " << j << " " << Nki << " " << Nmj << " " << DcW[i][j] << endl;
	error::fatal("DD neg in primitive C"); }
    }

  // wrapup.
  taylorData ch(lin,w,DcW);
  return ch;
};



			    
							      
/* ========================================================================== */
/*                                                                            */
/*   Section:Function                                                           */
/*                                                                            */
/* ========================================================================== */

/*implement unit*/
static int setZero(const domain& ,const domain& ,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  testAbs(DD,"setZero");
  return 1;
}
static lineInterval unitI(const domain& )
{
  static const interval one("1");
  return lineInterval(one);
}
static primitiveA scalr(unitI,setZero);

const Function Function::unit(&scalr);


Function Function::uni_compose // minor memory leak
(const univariate& f,const Function& g) {
  primitive_univariate* fp = new primitive_univariate(f,0);
  Function* fF = new Function(fp);
  Function* gF = new Function(g);
  primitive* uCp = new primitiveC
   (fF,gF,&Function::unit,&Function::unit,
    &Function::unit,&Function::unit,&Function::unit);
  Function uc(uCp);
  return uc;
  }

Function Function::uni_slot // minor memory leak
(const univariate& f,int slot) {
  primitive_univariate* fp = new primitive_univariate(f,slot);
  Function fF(fp);
  return fF;
  }


/*implement x1*x2 */
static lineInterval lineX1X2(const domain& x)
{
  //static const interval one("1");
  lineInterval h(interval(x.getValue(0),x.getValue(0)) * 
		 interval(x.getValue(1),x.getValue(1)));
  h.Df[0]= interval(x.getValue(1),x.getValue(1));
  h.Df[1]= interval(x.getValue(0),x.getValue(0));
  return h;
}
static int setX1X2DD(const domain& ,const domain& ,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  DD[1][0]=1.0;
  DD[0][1]=1.0;
  testAbs(DD,"setX1X2DD");
  return 1;
}
static primitiveA x1x2Prim(lineX1X2,setX1X2DD);
static const Function x1x2(&::x1x2Prim);


Function Function::product // minor memory leak.
(const Function& f,const Function& g) {
  Function* fF = new Function(f);
  Function* gF = new Function(g);
  primitive* pp = new primitiveC(&::x1x2,fF,gF,&Function::unit,
		&Function::unit,&Function::unit,&Function::unit);
  Function prod(pp);
  return prod;
}

Function Function::quotient
(const Function& f,const Function& g)
{
  return product(f,uni_compose(univariate::i_inv,g));
}



Function Function::compose // minor memory leak
(const Function& f,
 const Function& x1,const Function& x2,const Function& x3,
 const Function& x4, const Function& x5, const Function& x6)
{
  Function* fp = new Function(f);
  Function* x1p = new Function(x1);
  Function* x2p = new Function(x2);
  Function* x3p = new Function(x3);
  Function* x4p = new Function(x4);
  Function* x5p = new Function(x5);
  Function* x6p = new Function(x6);
  primitive* pp = new primitiveC(fp,x1p,x2p,x3p,x4p,x5p,x6p);
  Function g(pp);
  return g;
}

Function::Function(const Function& rhs)
{
  for (mapPrim::const_iterator it = rhs.data.begin(); it!= rhs.data.end(); ++it)
    data[it->first]=it->second;
}

// constructor from a primitive.
Function::Function(void* p) {
  static interval one("1");
  data[p] = one;
}

Function& Function::operator=(const Function& ) 
{
  error::message("assignment not implemented");
  return *this;
}

Function::~Function()
{
}

Function Function::operator*(const interval& x) const  {
  Function a(*this);
  for (mapPrim::const_iterator ia = a.data.begin();ia!=a.data.end();++ia) {
    a.data[ia->first] = ia->second * x;
  }
  return a;
}

Function Function::operator+(const Function& rhs) const {
  Function lhs(*this);
  mapPrim::iterator ilhs = lhs.data.begin();
  for (mapPrim::const_iterator irhs = rhs.data.begin();
       irhs!=rhs.data.end();++irhs) {
    ilhs = lhs.data.find(irhs->first);
    if (ilhs != lhs.data.end()) {      
      lhs.data[irhs->first] = ilhs->second + irhs->second;    
    }
    else {      lhs.data[irhs->first] = irhs->second;    }
  }
  return lhs;
}

taylorData Function::evalf4(const domain& w, const domain& x,const domain& y, const domain& z) const {
  taylorData t(w);
  for (mapPrim::const_iterator ia = this->data.begin();
      ia!=this->data.end();++ia) {
    t = taylorData::plus(t,
      taylorData::scale((*((primitive*)(ia->first))).evalf4(w,x,y,z),
				       ia->second));
  }
  return t;
};

taylorData Function::evalf
(const domain& x,const domain& z) const
{
  double w[6],y[6];
  int i;
  interMath::nearest();
  for (i=0;i<6;i++) y[i]=(z.getValue(i)+x.getValue(i))/2.0;
  interMath::up();
  for (i=0;i<6;i++) {
    w[i]=max(z.getValue(i)-y[i],
	     y[i]-x.getValue(i));
    assert(w[i] >= 0.0);
  }
  domain wD(w[0],w[1],w[2],w[3],w[4],w[5]);
  domain yD(y[0],y[1],y[2],y[3],y[4],y[5]);
  
  return Function::evalf4(wD,x,yD,z);
}

lineInterval Function::tangentAtEstimate(const domain& x) const {
  lineInterval t;
  lineInterval temp;
  for (mapPrim::const_iterator ia = this->data.begin();ia!=this->data.end();++ia) {
    temp =  ((primitive*)(ia->first))->tangentAtEstimate(x);
    t.f = t.f + temp.f * ia -> second;
    for (int i=0;i<6;i++) { t.Df[i] = t.Df[i] + temp.Df[i] * ia->second; }
  }
  return t;
};


/*
void Function::setReducibleState(int i)
{ reduState = i; }

int Function::getReducibleState() const
{ return reduState; }
*/

/*
int Function::hasDeltaDenom() const {
  Function u  (*this);
  for (mapPrim::const_iterator it = u.data.begin(); it!= u.data.end(); ++it) {
    primitive* p = (primitive*) (it->first);
    if (primHasDeltaDenom(p)) { return 1; } }
  return 0;
}
*/





///////// TESTING.

/* ========================================================================== */
/*                                                                            */
/*    Section:TESTING ROUTINES                                                        */
/*                                                                            */
/* ========================================================================== */

static int setAbsDihedral(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r = secondDerive::setAbsDihedral(X,Z,DD);
  if (r) { testAbs(DD,"setAbsDihedral"); }
  return r;
}

static int epsilonClose(double x,interval y,double epsilon)
{
  if (interMath::abs(y-interval(x,x))>epsilon)
    {
      cout << "close eps : " << interMath::abs(y-interval(x,x))
	   << " x: " << x << " y: " << y << endl<< flush;
      return 0;
    }
  return 1;
}

static int epsilonCloseDoubles(double x,double y,double epsilon)
{
  if (abs(y-x)>epsilon)
    {
      cout << "close-doubles eps: " << abs(y-x)
	   << " x: " << x << "  y: " << y << endl<< flush;
      return 0;
    }
  return 1;
}



static lineInterval lineX1(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(0),x.getValue(0)));
  h.Df[0]=one;
  return h;
}

void Function::selfTest()
{
  cout << " -- loading taylorData" << endl << flush;


  /* test primitiveA. */
  domain d(2.0,2.1,2.2,2.3,2.4,2.5);
  primitiveA p(lineX1,setZero);

  Function f(&p);
  //cout << "B" << flush;
  taylorData td = f.evalf(d,d);
  /* cout << "C" << flush;
  cout << td.upperBound() << endl << flush;
  cout << td.lowerBound() << endl << flush;
  cout << Function::unit.evalf(d,d).upperBound() << endl << flush;
  cout << "D" << flush;
  */
  Function g = Function::mk_raw(unitI,setZero);
  //cout << g.evalf(d,d).upperBound() << endl << flush;

  /*test unit*/  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    taylorData t = Function::unit.evalf(x,z);
    if ((!t.upperBound()==1) || (!t.lowerBound()==1))
      cout << "unit fails = " << t.upperBound()<<" " << t.lowerBound()<<endl;
    for (int i=0;i<6;i++) if ((t.upperPartial(i)!=0)||(t.lowerPartial(i)!=0))
			    cout << "unitp fails = " << t.upperPartial(i)<<" " << t.lowerPartial(i)<<endl;
  }

  /* test monomial */   { 
    domain x(1.1,1.2,1.3,1.4,1.5,1.6);
    int m[6] = {7,12,1,0,2,3};
    //taylorData at = Function::mk_monomial(m).evalf(x,x);
    taylorData at = Function::mk_monomial(7,12,1,0,2,3).evalf(x,x);
    double mValue= 208.16588972375973;
    double mathValueD[6]={1324.692025514837,2081.6588972376016,
      160.1276074798155,0,277.5545196316802,390.3110432320503};
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "monomial  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "monomial D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


	/*test monomial DD */ {
	// constants computed in Mathematica.
	cout.precision(16);
	domain x(1.1,1.2,1.3,1.4,1.5,1.6);
	double DDmf[6][6] = {{
	    7225.592866444565,13246.920255148372,1018.9938657806439,0,
	    1766.2560340197826,2483.7975478403196},
			     {13246.920255148372,19081.87322467802,1601.2760747981552,0,
			      2775.545196316802,3903.1104323205036},
			     {1018.9938657806439,1601.2760747981552,0,0,213.50347663975396,
			      300.23926402465406},{0,0,0,0,0,0},
			     {1766.2560340197826,2775.545196316802,213.50347663975396,0,
			      185.0363464211201,520.4147243094003},
			     {2483.7975478403196,3903.1104323205036,300.23926402465406,0,
			      520.4147243094003,487.8888040400628}};
        taylorData g = Function::mk_monomial(7,12,1,0,2,3).evalf(x,x);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
	    if (!epsilonCloseDoubles(DDmf[i][j],g.DD[i][j],1.0e-8)) {
		cout << "monomial DD " << i << " " << j << " " << g.DD[i][j];
		cout << " eps: " << (DDmf[i][j] - g.DD[i][j]) << endl;
		error::message("monomial failure");
	      }
	  }
  }


  /* test uni_compose */ {
    Function x2 = 
      Function::uni_slot(univariate::i_pow1,1);
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 2.04939015319192;
    double mathValueD[6]={0,0.24397501823713327,0,0,0,0};
    Function t = Function::uni_compose(univariate::i_sqrt,x2);
    taylorData at = t.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "uni  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "uni D " << i << "++ fails " << at.upperPartial(i) << endl;
    }    
    Function y2= Function::uni_slot(univariate::i_sqrt,1);
    taylorData at2 = y2.evalf(x,x);
    if (!epsilonCloseDoubles(at2.upperBound(),mValue,1.0e-8))
      cout << "uni2  fails " << endl;
  }


  /* test prod */ {

    Function dih = Function::mk_raw(linearization::dih,setAbsDihedral);
    Function y1 = Function::uni_slot(univariate::i_sqrt,0);
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 2.4623610348104914;
    double mathValueD[6]={0.40443775297783785,-0.10690140741833755,
   -0.11756239286152013,0.32047195412373986,-0.0917206840314374,
			  -0.10213991072724367};
    Function t = 
      Function::product(y1,dih);
    taylorData at = t.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "uni  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "uni D " << i << "++ fails " << at.upperPartial(i) << endl;
    }    
  }


  cout << " -- done loading taylorData" << endl << flush;
}
