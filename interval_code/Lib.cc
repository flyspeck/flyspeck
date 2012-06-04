/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                     */
/* Split off from taylorData 2012-6 */
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
#include "Lib.h"
 
using namespace std;
using namespace tr1;

/* ========================================================================== */
/*                                                                            */
/*   Section:FunctionLibrary                                                            */
/*                                                                            */
/* ========================================================================== */



static inline double max(double x,double y)
{ return (x>y ? x : y); }

static inline double dabs(const interval x) {
  return interMath::sup(interMath::max(x,-x));
}

static int copy(double DD[6][6],const double sec[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++)
			  DD[i][j]=sec[i][j];
  return 1;
}

static void testAbs(double DD[6][6],const char* s) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD[i][j] < 0) {
	error::message("negative absolute value detected " );
	cout << s << " " << DD[i][j] << " " << i << " " << j << endl;
      }
    }
}

static void intervalToAbsDouble(const interval DDx[6][6],double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 	
			  DD[i][j]= dabs(DDx[i][j]);
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


/* ========================================================================== */
/*                                                                            */
/*   Section:L namespace                                            */
/*                                                                            */
/* ========================================================================== */


namespace L {

  Function uni(const univariate& u,const Function& f) {
   return Function::uni_compose(u,f);
  }

  static const univariate i_inv = univariate::i_inv;
  static const univariate i_pow2 = univariate::i_pow2;
  static const univariate i_pow1 = univariate::i_pow1;
  static const univariate i_pow0 = univariate::i_pow0;
  static const univariate i_matan = univariate::i_matan;
  static const univariate i_sqrt = univariate::i_sqrt;
  static const univariate i_acos = univariate::i_acos;
  static const univariate i_sin = univariate::i_sin;
  static const univariate i_asin = univariate::i_asin;

  static const interval h0("1.26");
  static const interval sqrt3("1.7320508075688772935");
  static const interval sqrt2("1.4142135623730950488");
  static const interval quarter("0.25");
  static const interval half("0.5");
  static const interval one("1");
  static const interval mone("-1");
  static const interval two ("2");
  static const interval three ("3");
  static const interval four ("4");
  static const interval eight ("8");
  static const interval sixteen ("16");
  static const interval pi("3.1415926535897932385");
  static const interval const1 ("0.175479656091821810");
  static const interval sol0("0.5512855984325308079421");
  static const interval mm1("1.01208086842065466") ;
  static const interval mm2("0.0254145072695089280");

  static const interval sqrt8 ("2.8284271247461900976");
  static const interval hminus("1.2317544220903043901");
  static const interval arc_hhn("0.81611135460255697143595");

  static const interval yStrongDodec("2.1029244484765344");
  static const interval aStrongDodec("-0.581169206221610");
  static const interval bStrongDodec("0.023248513304698");
  static const interval rh0 = one/(h0 - one);

  };


 Function operator*(const Function& f,const Function& g) {
   return Function::product(f,g);
 }

 Function operator/(const Function& f,const Function& g) {
   return Function::product(f,L::uni(L::i_inv,g));
 }

  static const Function operator*(const Function& t,int j) {
    return t * interval(j * 1.0, j * 1.0);
  }

  static const Function operator*(int j,const Function& t) {
    return t * interval(j * 1.0, j * 1.0);
  }

  static const Function operator-
  (const Function& u,const Function& t) {
    return u + t * L::mone;
  }



/* implement promote1_to_6 */
const Function Lib::promote1_to_6(const univariate& f) {
  return Function::uni_slot(f,0);
}

/* implement unit */
const Function Lib::unit(Function::unit);

const Function Lib::two6 = Lib::unit * L::two;

const Function Lib::constant6(const interval& i) {
  return Lib::unit * i;
}
/*implement x1,..,x6 */


/* ========================================================================== */
/*                                                                            */
/*   Section:L namespace                                            */
/*                                                                            */
/* ========================================================================== */


const Function Lib::x1 = 
  Lib::promote1_to_6(L::i_pow1);
const Function Lib::x2 = 
  Function::uni_slot(L::i_pow1,1);
const Function Lib::x3 = 
  Function::uni_slot(L::i_pow1,2);
const Function Lib::x4 = 
  Function::uni_slot(L::i_pow1,3);
const Function Lib::x5 = 
  Function::uni_slot(L::i_pow1,4);
const Function Lib::x6 = 
  Function::uni_slot(L::i_pow1,5);

/*
 Function Lib::rotate2(const Function& f) {
  return Function::compose
  (f,
   Lib::x2,Lib::x3,Lib::x1,
   Lib::x5,Lib::x6,Lib::x4);
 }

 Function Lib::rotate3(const Function& f) {
  return Function::compose
  (f,
   Lib::x3,Lib::x1,Lib::x2,
   Lib::x6,Lib::x4,Lib::x5);
 }

 Function Lib::rotate4(const Function& f) {
  return Function::compose
    (f,
  Lib::x4  , Lib::x2, Lib::x6,
  Lib::x1 , Lib::x5,  Lib::x3);
}

 Function Lib::rotate5(const Function& f) {
  return Function::compose
    (f,
     Lib::x5  , Lib::x3, Lib::x4,
     Lib::x2 , Lib::x6, Lib::x1);
}

 Function Lib::rotate6(const Function& f) {
   return Function::compose
    (f,
     Lib::x6  , Lib::x1, Lib::x5,
     Lib::x3 , Lib::x4, Lib::x2);
}
*/

Function uni(const univariate& u,const Function& f) {
   return Function::uni_compose(u,f);
  };

/*implement y1,...,y6 */
const Function Lib::y1= Function::uni_slot(univariate::i_sqrt,0);
/*
const Function Lib::y2= Lib::rotate2(y1);
const Function Lib::y3= Lib::rotate3(y1);
const Function Lib::y4= Lib::rotate4(y1);
const Function Lib::y5= Lib::rotate5(y1);
const Function Lib::y6= Lib::rotate6(y1);
*/

// univariates:

/* implement gchi (univariate) */ 
// gchi (sqrt x) = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (sqrt x) * mm2 /pi)/ &13
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
univariate i_gchi = univariate::i_sqrt* i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;

/*   `!y. lfun y = ( h0 - y)*rh0` */
univariate i_lfun = 
  (univariate::i_pow0 * L::h0 + univariate::i_pow1 * L::mone)*L::rh0;

/* `!y. rho y = y * (const1 * rh0 * (#0.5)) + (&1 - const1 * rh0)`*/
static const univariate i_rho = 
  univariate::i_pow1 * (L::const1 * L::rh0 * L::half) + 
  univariate::i_pow0 * (L::one - L::const1 * L::rh0);

/*   `!y. flat_term_x y = (sqrt y - &2 * h0) * rh0 * sol0 * (#0.5)` */
static const univariate i_flat_term_x = (univariate::i_sqrt + univariate::i_pow0 * (L::mone*L::two * L::h0)) * ( L::rh0 * L::sol0 * L::half);


/* implement halfbump_x (univariate) */
/*
 |- !x. &0 <= x
         ==> halfbump_x x =
             --(&4398119 / &2376200) +
             &17500 / &11881 * sqrt x - &31250 / &106929 * x
*/
static interval a0("-4398119");
static interval b0("2376200");
static interval a1("17500");
static interval b1("11881");
static interval a2("-31250");
static interval b2("106929");
univariate i_halfbump_x = univariate::i_pow0 * (a0 / b0) +
  univariate::i_sqrt * (a1 / b1) + univariate::i_pow1 * (a2 / b2);
//const Function Lib::halfbump_x1 = 
//  Function::uni_slot(::i_halfbump_x,0);
//const Function Lib::halfbump_x4 = 
//  Function::uni_slot(::i_halfbump_x,3);

/* implement gchi (univariate) */ 
// gchi (sqrt x) = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (sqrt x) * mm2 /pi)/ &13
/*
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
univariate i_gchi = L::i_sqrt* i_gchi_c1 + L::i_pow0 * i_gchi_c0;
*/

/*
const Function Lib::gchi1_x = 
  L::uni(::i_gchi,Lib::y1) * Lib::dih_x;
*/


/*implement delta */
static int setAbsDelta(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  interval DDh[6][6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  secondDerive::setDelta(X,Z,DDh);
  intervalToAbsDouble(DDh,DD);
  testAbs(DD,"setAbsDelta");
  return 1;
}
//primitiveA deltaPrimitive(linearization::delta,setAbsDelta);
const Function Lib::delta_x= Function::mk_raw(linearization::delta,setAbsDelta);// (&::deltaPrimitive);


/*implement ups_126*/
static int setAbsUps(const domain& x,const domain& z,double DD[6][6])
{
  double xa[6],za[6];
  for (int i=0;i<6;i++) {
    xa[i] = x.getValue(i);
    za[i] = z.getValue(i);
  }
  interval DDi[6][6];
  secondDerive::setU126(xa,za,DDi);
  intervalToAbsDouble(DDi,DD);
  return 1;
}
static const Function ups_126= Function::mk_raw(linearization::ups_126,setAbsUps);

static const Function ups_135 = Function::compose
  (ups_126, Lib::x1,Lib::x3,Lib::unit, Lib::unit,Lib::unit,Lib::x5);

// implement edge_flat2_x.
const Function bx_neg_quadratic = 
  Lib::x1*(Lib::x2 + Lib::x3 + Lib::x5 + Lib::x6) -
  Lib::x1 * Lib::x1 - (Lib::x3 - Lib::x5)*(Lib::x2 - Lib::x6) ;
const Function disc_quadratic =  uni(L::i_sqrt, ups_126 * ups_135 );
const Function ax2_inv_quadratic = uni(L::i_inv,Lib::x1 * L::two) ;


const Function edge_flat2_x = (bx_neg_quadratic + disc_quadratic) * ax2_inv_quadratic;
//const Function edge_flat_x = (uni(i_sqrt,edge_flat2_x));

/*implement eta2_126*/
static int setEta2_126(const domain& x,const domain& z,double DD[6][6])
{
  double xa[6],za[6];
  for (int i=0;i<6;i++) {
    xa[i] = x.getValue(i);
    za[i] = z.getValue(i);
  }
  secondDerive::setAbsEta2_x_126(xa,za,DD);
  return 1;
}
const Function Lib::eta2_126= 
  Function::mk_raw(linearization::eta2_126,setEta2_126);

/*implement delta_x4*/
static int setAbsDeltaX4(const domain& x,const domain& z,double DDf[6][6]) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DDf[i][j]= 2.0; }
  // all second partials are pm 0,1,2.  
}
const Function Lib::delta_x4= 
  Function::mk_raw(linearization::delta_x4,setAbsDeltaX4);

/*implement dih_x */
static int setAbsDihedral(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r = secondDerive::setAbsDihedral(X,Z,DD);
  if (r) { testAbs(DD,"setAbsDihedral"); }
  return r;
}
const Function Lib::dih_x = Function::mk_raw(linearization::dih,setAbsDihedral);

/*implement sol_x */
static int setSol(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i,j;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6],DDx[6][6];
  if (!(secondDerive::setSqrtDelta(X,Z,s,Ds,DDs))) return 0;
  if (!(secondDerive::setSolid(X,Z,s,Ds,DDs,DDx))) return 0;
  for (i=0;i<6;i++) for (j=i;j<6;j++)
		      DD[i][j]=dabs(DDx[i][j]);
  for (i=0;i<6;i++) for (j=0;j<i;j++) DD[i][j]=DD[j][i];
  return 1;
}
const Function Lib::sol_x= Function::mk_raw(linearization::solid,setSol);


/* ========================================================================== */
/*                                                                            */
/*    Section:TESTING ROUTINES                                                        */
/*                                                                            */
/* ========================================================================== */

static bool epsilonCloseDoubles(const char* s, double x,double y,double epsilon)
{
  if (abs(y-x)>epsilon)
    {
      cout << s << ": " ;
      cout << "diff: " << abs(y-x)
	   << " external value: " << x << "  value here: " << y << endl<< flush;
      error::message("error encountered in loading Lib");
      return false;
    }
  return true;
}

static void epsValue(const char* s,const Function& f,double x) {
  double eps = 1.0e-8;
  domain d(6.36,4.2,4.3,4.4,4.5,4.6);
  double y = f.evalf(d,d).upperBound();
  epsilonCloseDoubles(s,x,y,eps);
}

void Lib::selfTest()
{
  cout << " -- loading Lib routines " << endl << flush;
  epsValue("unit",Lib::unit,1.0);
  epsValue("x1",Lib::x1,6.36);
  epsValue("x2",Lib::x2,4.2);
  epsValue("x3",Lib::x3,4.3);
  epsValue("x4",Lib::x4,4.4);
  epsValue("x5",Lib::x5,4.5);
  epsValue("x6",Lib::x6,4.6);
  epsValue("y1",Lib::y1,sqrt(6.36));
  cout << " -- done loading Lib" << endl << flush;
  
}

