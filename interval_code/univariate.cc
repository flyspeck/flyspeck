/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 2010-09-07 */
/* ========================================================================== */

//#include <map>
#include <utility>
#include <tr1/unordered_map>
#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
#include <float.h>
#include <time.h>
}
#include "error.h"
#include "interval.h"
#include "univariate.h"

using namespace std;
using namespace tr1;

class uniprimitive
{
public:
	interval (*f)(const interval&);
	interval (*df)(const interval&);
	interval (*ddf)(const interval&);
public:

  interval eval(const interval&,int n) const;

  uniprimitive(interval (*)(const interval& ),interval(*) (const interval&),
		interval(*) (const interval&));

  static void selfTest();

};


interval uniprimitive::eval(const interval& x,int n) const
{
  return (n ==0 ?  (*f)(x) : (n == 1 ? (*df)(x) : (*ddf)(x) ) );
}

uniprimitive::uniprimitive(interval (*f0)(const interval& ),interval(*df0) (const interval&),
	     interval(*ddf0) (const interval&)) {
  f = f0;
  df = df0;
  ddf0 = ddf0;
}

//sqrt 

static interval usqrt(const interval& x) {
  return interMath::sqrt(x);
}

static interval Dsqrt(const interval& x) {
	static const interval one("1");
	static const interval two("2");
	return one/(two * interMath::sqrt(x));
}

static interval DDsqrt(const interval& x) {
	static const interval one("1");
	static const interval four("4");
	return - one/(four * x * interMath::sqrt(x));
}

static uniprimitive psqrt(usqrt,Dsqrt,DDsqrt);


// atan 
static interval uatan(const interval& x) {
  return interMath::atan(x);
}

static interval Datan(const interval& x) {
	static const interval one("1");
	return one/(one + x * x);
}

static interval DDatan(const interval& x) {
	static const interval one("1");
	static const interval two("2");
	interval t = one + x*x;
	return - two*x /(t*t);
}

static uniprimitive patan(uatan,Datan,DDatan);


// asin,

//"ASN_ATN",|- !x. -- &1 < x /\ x < &1 ==> asn x = atn (x / sqrt (&1 - x pow 2))

static void atrig_domain_check(const interval& x,char* ch) {
  if (interMath::inf(x) <= -1.0 || interMath::sup(x) >= 1.0) {
    cout << "bad argument for trig " << ch << endl << flush;
    error::fatal("domain error, aborting ");
  }
} 

static interval uasin(const interval& x) {
  atrig_domain_check(x,"asin");
  static const interval one("1");
  return interMath::atan(x / usqrt(one - x * x));
}

static interval Dasin(const interval& x) {
  atrig_domain_check(x,"Dasin");
  static const interval one("1");
  return one/usqrt(one - x*x);
}

static interval DDasin(const interval& x) {
  atrig_domain_check(x,"DDasin");
  static const interval one("1");
  interval t = one  - x* x;
  return x / (t * usqrt(t));
}

 static uniprimitive pasin(uasin,Dasin,DDasin);

//acos

// "ACS_ASN", |- !x. -- &1 <= x /\ x <= &1 ==> acs x = pi / &2 - asn x);

static interval uacos(const interval& x) {
  static interval pi2("1.570796326794896619");
  atrig_domain_check(x,"acos");
  return pi2 - uasin(x);
}

static interval Dacos(const interval& x) {
  atrig_domain_check(x,"Dacos");
  return - Dasin(x);
}

static interval DDacos(const interval& x) {
  atrig_domain_check(x,"DDacos");
  return - DDasin(x);
}

static uniprimitive pacos(uacos,Dacos,DDacos);

// sin , cos

static void trig_domain_check(const interval& x,char* ch) {
  static double pi_minus_eps = 3.1415926;
  if (interMath::inf(x) <= -pi_minus_eps || interMath::sup(x) >= pi_minus_eps) {
    cout << "bad argument for trig " << ch << endl << flush;
    error::fatal("domain error, aborting ");
  }
} 

 static int meets(const interval& x,const interval& y) {
   return (!(x < y)) && (!(y < x));
 }

static interval sin_p(double x) {
  interMath::up();
  double a = sin(x);
  interMath::down();
  double b = sin(x);
  interval t(min(a,b),max(a,b));
  return t;
}

static interval cos_p(double x) {
  interMath::up();
  double a = cos(x);
  interMath::down();
  double b = cos(x);
  interval t(min(a,b),max(a,b));
  return t;
}

static interval usin(const interval& x) {
  static interval one ("1");
  static interval pi2("1.570796326794896619");
  trig_domain_check(x,"sin");
  interval t = interMath::combine(sin_p(interMath::inf(x)),sin_p(interMath::sup(x)));
  t =  (meets(x,pi2) ? interMath::combine(t,one) : t);
  t = (meets(x, - pi2) ? interMath::combine(t,- one) : t);
  return t;
}

static interval ucos(const interval& x) {
  static interval zero("0");
  static interval one ("1");
  trig_domain_check(x,"cos");
  interval t = interMath::combine(cos_p(interMath::inf(x)),cos_p(interMath::sup(x)));
  t =  (meets(x,zero) ? interMath::combine(t,one) : t);
  return t;
}

static interval Dsin(const interval& x) {
  return ucos(x);
}

static interval DDsin(const interval& x) {
  return - usin(x);
}

static interval Dcos(const interval& x) {
  return - usin(x);
}

static interval DDcos(const interval& x) {
  return - ucos(x);
}

 static uniprimitive pcos(ucos,Dcos,DDcos);

 static uniprimitive psin(usin,Dsin,DDsin);

//pow0 

static interval pow0(const interval& x) {
  static const interval one("1");
  return one;
}

static interval Dpow0(const interval& x) {
	static const interval zero("0");
	return zero;
}

static interval DDpow0(const interval& x) {
	static const interval zero("0");
	return zero;
}

static uniprimitive ppow0(pow0,Dpow0,DDpow0);


//pow1 

static interval pow1(const interval& x) {
  return x;
}

static interval Dpow1(const interval& x) {
	static const interval one("1");
	return one;
}

static interval DDpow1(const interval& x) {
	static const interval zero("0");
	return zero;
}

static uniprimitive ppow1(pow1,Dpow1,DDpow1);



// pow2

static interval pow2(const interval& x) {
  return x*x;
}

static interval Dpow2(const interval& x) {
  static interval two("2");
  return two*x;
}

static interval DDpow2(const interval& x) {
  static interval two("2");
  return two;
}

 static uniprimitive ppow2(pow2,Dpow2,DDpow2);

// pow3

static interval pow3(const interval& x) {
  return x*x*x;
}

static interval Dpow3(const interval& x) {
  static interval three("3");
  return three*x*x;
}

static interval DDpow3(const interval& x) {
  static interval six("6");
  return six*x;
}

 static uniprimitive ppow3(pow3,Dpow3,DDpow3);

// pow4

static interval pow4(const interval& x) {
  return pow2(x) * pow2(x);
}

static interval Dpow4(const interval& x) {
  static interval four("4");
  return four* pow3(x);
}

static interval DDpow4(const interval& x) {
  static interval twelve("12");
  return twelve* x*x;
}

 static uniprimitive ppow4(pow4,Dpow4,DDpow4);

// IMPLEMENT UNIVARIATE CLASS


univariate::univariate(const univariate& rhs)
{
  for (mapType::const_iterator it = rhs.data.begin(); it!= rhs.data.end(); ++it)
      data[it->first]=it->second;
}

univariate::univariate(void* p) {
  static interval one("1");
  data[p] = one;
}

univariate univariate::operator+(const univariate& rhs) const {
  univariate lhs(*this);
  mapType::iterator ilhs = lhs.data.begin();
  for (mapType::const_iterator irhs = rhs.data.begin();irhs!=rhs.data.end();++irhs) {
    ilhs = lhs.data.find(irhs->first);
    if (ilhs != lhs.data.end()) {      
      lhs.data[irhs->first] = ilhs->second + irhs->second;    
    }
    else {      lhs.data[irhs->first] = irhs->second;    }
  }
  return lhs;
}

univariate univariate::operator*(const interval& x) const  {
  univariate a(*this);
  for (mapType::const_iterator ia = a.data.begin();ia!=a.data.end();++ia) {
    a.data[ia->first] = ia->second * x;
  }
  return a;
}

  univariate::~univariate() {};



interval univariate::eval(const interval& x, int n) const {
  interval t("0");
  for (mapType::const_iterator ia = this->data.begin();ia!=this->data.end();++ia) {
    t = t + (*((uniprimitive*)(ia->first))).eval(x,n) * ia->second;
  }
  return t;
};

// static const univariate pow0, pow1,pow2,pow3,pow4,sqrt, atan, asin, sin, cos;

//static void univariate::selfTest() {};

static const univariate::univariate i_pow0(&ppow0);
static const univariate::univariate i_pow1(&ppow1);
static const univariate::univariate i_pow2(&ppow2);
static const univariate::univariate i_pow3(&ppow3);
static const univariate::univariate i_pow4(&ppow4);
static const univariate::univariate i_sqrt(&psqrt);
static const univariate::univariate i_atan(&patan);
static const univariate::univariate i_asin(&pasin);
static const univariate::univariate i_acos(&pacos);
static const univariate::univariate i_sin(&psin);
static const univariate::univariate i_cos(&pcos);
//,pow1, pow2,pow3,pow4,sqrt, atan, asin, sin, cos;


static int epsilonClose(double x,double y,double epsilon)
    {
      double t = abs(y-x);
      if (t>epsilon)
        {
	  cout << "close : " << t << " " << x << " " << y << endl<< flush;
        return 0;
        }
    return 1;
    }

static int epsilon3(double f,double df,double ddf,interval x,double epsilon) {
  return 0; // fill in.
}


void univariate::selfTest() 
	{
	cout << " -- loading univariate routines " << endl;
	}


