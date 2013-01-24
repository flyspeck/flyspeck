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
/*   Section: General functions                                               */
/*                                                                            */
/* ========================================================================== */

static inline double max(double x,double y)
{ return (x>y ? x : y); }

static inline double dabs(const interval x) {
  return interMath::sup(interMath::max(x,-x));
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

/* ========================================================================== */
/*                                                                            */
/*   Section:L namespace                                            */
/*                                                                            */
/* ========================================================================== */

namespace L {

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
  static const interval twentyfour("24");
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


/* ========================================================================== */
/*                                                                            */
/*   Section:Library Functions                                            */
/*                                                                            */
/* ========================================================================== */

  Function Lib::uni(const univariate& u,const Function& f) {
    Function t = Function::uni_compose(u,f);
    return t;
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

/*implement y1 */
const Function Lib::y1= Function::uni_slot(univariate::i_sqrt,0);

// univariates:

/* implement gchi (univariate) */ 
// gchi x = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (x) * mm2 /pi)/ &13
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
const univariate Lib::i_gchi = univariate::i_pow1* i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;

/*   `!y. lfun y = ( h0 - y)*rh0` */
const univariate Lib::i_lfun = 
  (univariate::i_pow0 * L::h0 + univariate::i_pow1 * L::mone)*L::rh0;

/* `!y. rho y = y * (const1 * rh0 * (#0.5)) + (&1 - const1 * rh0)`*/
const univariate Lib::i_rho = 
  univariate::i_pow1 * (L::const1 * L::rh0 * L::half) + 
  univariate::i_pow0 * (L::one - L::const1 * L::rh0);

/*   `!y. flat_term_x y = (sqrt y - &2 * h0) * rh0 * sol0 * (#0.5)` */
const univariate Lib::i_flat_term_x = (univariate::i_sqrt + univariate::i_pow0 * (L::mone*L::two * L::h0)) * ( L::rh0 * L::sol0 * L::half);

/*   new_definition `gamma2_x_div_azim_v2 m x = (&8 - x)* sqrt x / (&24) -
  ( &2 * (&2 * mm1/ pi) * (&1 - sqrt x / sqrt8) - 
      (&8 * mm2 / pi) * m * lfun (sqrt x / &2))`;;  */
const univariate Lib::i_gamma2_x_div_azim_v2(const interval& m) {
  //  static const interval mm1x("0.644310692071541214963158104232"); // 2x fixed Jan 23, 2013.
  static const interval mm1x("1.28862138414308242992631620846"); // = 4 mm1 /Pi
  static const interval mm2x("0.0647175113309960600618528362429"); // = 8 mm2 / Pi.
  univariate t =     
   (L::i_sqrt * L::eight + univariate::i_pow3h2 * L::mone)*
     (L::one/ L::twentyfour) +
  ( L::i_sqrt * (L::one/ L::sqrt8) + L::i_pow0 * L::mone) * mm1x + 
    (L::i_sqrt *L::half*L::mone + L::i_pow0 * L::h0 )
  * 		       (L::rh0 * m * mm2x); 
  return t;
};

/*const Function gamma2_x1_div_a(const interval& m) {
  univariate t = i_gamma2_x_div_azim(m);
  return promote1_to_6(t);
  }*/

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
const univariate Lib::i_halfbump_x = univariate::i_pow0 * (a0 / b0) +
  univariate::i_sqrt * (a1 / b1) + univariate::i_pow1 * (a2 / b2);

/* implement halfbump_x1 */
const Function Lib::halfbump_x1 = Lib::promote1_to_6(Lib::i_halfbump_x);

  // num1
  /* thm =  |- !x1 x2 x3 x4 x5 x6.         num1 x1 x2 x3 x4 x5 x6 =
         &64 * x1 * x4 -          &32 * x2 * x4 -         &32 * x3 * x4 -
         &4 * x1 * x4 pow 2 -          &32 * x2 * x5 +         &32 * x3 * x5 +
         &4 * x2 * x4 * x5 +         &32 * x2 * x6 - &32 * x3 * x6 +         &4 * x3 * x4 * x6 */
  static const interval t64("64");
  static const interval t32("32");
  static const interval t16("16");

const Function Lib::num1 = 
    Lib::x1 * Lib::x4 * t64 +  Lib::x2 * Lib::x4 *L::mone * t32 +  
    Lib::x3 * Lib::x4 *L::mone * t32 
    + Lib::x1 * Lib::x4 * Lib::x4 * L::mone * L::four  +  
    Lib::x2 * Lib::x5 * L::mone * t32 + Lib::x3 * Lib::x5 * t32
    + Lib::x2 * Lib::x4 * Lib::x5  * L::four +  Lib::x2 * Lib::x6 * t32 + 
    Lib::x3 * Lib::x6 * L::mone * t32 +  Lib::x3 * Lib::x4 * Lib::x6 * L::four;

/*implement deltaLC */
const Function Lib::delta_y_LC = Function::mk_LC(wide::delta_y);

/*implement mdtau_y_LC */
const Function Lib::mdtau_y_LC= Function::mk_LC(wide::mdtau_y);

/*implement mdtau2uf_y_LC */
const Function Lib::mdtau2uf_y_LC= Function::mk_LC(wide::mdtau2uf_y);

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
const Function Lib::delta_x= Function::mk_raw(linearization::delta,setAbsDelta);

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
static const Function ups_126= 
  Function::mk_raw(linearization::ups_126,setAbsUps);

static const Function ups_135 = Function::compose
  (ups_126, Lib::x1,Lib::x3,Lib::unit, Lib::unit,Lib::unit,Lib::x5);

// implement edge_flat2_x.
const Function bx_neg_quadratic = 
  Lib::x1*(Lib::x2 + Lib::x3 + Lib::x5 + Lib::x6) -
  Lib::x1 * Lib::x1 - (Lib::x3 - Lib::x5)*(Lib::x2 - Lib::x6) ;
const Function disc_quadratic =  Lib::uni(L::i_sqrt, ups_126 * ups_135 );
const Function ax2_inv_quadratic = Lib::uni(L::i_inv,Lib::x1 * L::two) ;

const Function Lib::edge_flat2_x = 
  (bx_neg_quadratic + disc_quadratic) * ax2_inv_quadratic;

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

/*implement rad2*/
static int setAbsRad2(const domain& x, const domain& z, double DD[6][6]) {
  double  X[6],Z[6];
  int i;
  double DD1[6][6], DD2[6][6];
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r1 = secondDerive::setAbsEta2_x_126(X,Z,DD1);
  int r2 = secondDerive::setChi2over4uDelta(X,Z,DD2);
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j] = DD1[i][j] + DD2[i][j]; }
  if (r1+r2) { testAbs(DD,"setAbsRad2"); }
  return r1+r2;
}
const Function Lib::rad2_x= Function::mk_raw(linearization::rad2,setAbsRad2);

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

/*implement truncate_dih_x*/
/*
static int setAbsTruncateDihedral(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r = secondDerive::setAbsTruncateDihedral(X,Z,DD);
  if (r) { testAbs(DD,"setAbsDihedral"); }
  return r;
}
const Function truncate_dih_x_014= Function::mk_raw(linearization::truncate_dih,setAbsTruncateDihedral);

 const Function Lib::truncate_dih_x(const interval& c) {
   static const interval c14("0.14");
   if (c.hi > c.lo + 1.0e-8 || c.lo < c14.lo - 1.0e-8 || c.hi > c14.hi + 1.0e-8) {
     error::message("truncate_dih_x 0.14 out of range");
   }
   return truncate_dih_x_014;
 }
*/

/*implement truncate_vol_x */ 
 /*
static interval one("1");
static interval twelve("12");
static interval f12 =  (one/ twelve);
const Function truncate_vol_x_014 = 
  Lib::uni(univariate::i_truncate_sqrt,Lib::delta_x) *f12;

 const Function Lib::truncate_vol_x(const interval& c) {
   static const interval c14("0.14");
   if (c.hi > c.lo + 1.0e-8 || c.lo < c14.lo - 1.0e-8 || c.hi > c14.hi + 1.0e-8) {
     error::message("truncate_dih_x 0.14 out of range");
   }
   return truncate_vol_x_014;
 }
 */

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

//static const Function operator*(const Function& t,int j) {
//  return t * interval(j * 1.0, j * 1.0);
//}

static const Function operator*(int j,const Function& t) {
  return t * interval(j * 1.0, j * 1.0);
}

const Function Lib::num2 = 
  (-2048)*Function::mk_monomial(0,0,1,0,0,3) + 6144*Function::mk_monomial(0,0,1,0,1,2) - 6144*Function::mk_monomial(0,0,1,0,2,1) + 
   2048*Function::mk_monomial(0,0,1,0,3,0) + 10240*Function::mk_monomial(0,0,1,1,0,2) + 128*Function::mk_monomial(0,0,1,1,0,3) - 
   4096*Function::mk_monomial(0,0,1,1,1,1) - 1664*Function::mk_monomial(0,0,1,1,1,2) - 6144*Function::mk_monomial(0,0,1,1,2,0) + 
   1920*Function::mk_monomial(0,0,1,1,2,1) - 384*Function::mk_monomial(0,0,1,1,3,0) - 6144*Function::mk_monomial(0,0,1,2,0,1) - 
   896*Function::mk_monomial(0,0,1,2,0,2) - 16*Function::mk_monomial(0,0,1,2,0,3) + 6144*Function::mk_monomial(0,0,1,2,1,0) - 
   256*Function::mk_monomial(0,0,1,2,1,1) + 160*Function::mk_monomial(0,0,1,2,1,2) + 1152*Function::mk_monomial(0,0,1,2,2,0) - 
   144*Function::mk_monomial(0,0,1,2,2,1) - 2048*Function::mk_monomial(0,0,1,3,0,0) + 384*Function::mk_monomial(0,0,1,3,0,1) + 
   64*Function::mk_monomial(0,0,1,3,0,2) - 1152*Function::mk_monomial(0,0,1,3,1,0) + 128*Function::mk_monomial(0,0,1,3,1,1) - 
   8*Function::mk_monomial(0,0,1,3,1,2) + 384*Function::mk_monomial(0,0,1,4,0,0) - 48*Function::mk_monomial(0,0,1,4,0,1) + 
   2048*Function::mk_monomial(0,1,0,0,0,3) - 6144*Function::mk_monomial(0,1,0,0,1,2) + 6144*Function::mk_monomial(0,1,0,0,2,1) - 
   2048*Function::mk_monomial(0,1,0,0,3,0) - 6144*Function::mk_monomial(0,1,0,1,0,2) - 384*Function::mk_monomial(0,1,0,1,0,3) - 
   4096*Function::mk_monomial(0,1,0,1,1,1) + 1920*Function::mk_monomial(0,1,0,1,1,2) + 10240*Function::mk_monomial(0,1,0,1,2,0) - 
   1664*Function::mk_monomial(0,1,0,1,2,1) + 128*Function::mk_monomial(0,1,0,1,3,0) + 6144*Function::mk_monomial(0,1,0,2,0,1) + 
   1152*Function::mk_monomial(0,1,0,2,0,2) - 6144*Function::mk_monomial(0,1,0,2,1,0) - 256*Function::mk_monomial(0,1,0,2,1,1) - 
   144*Function::mk_monomial(0,1,0,2,1,2) - 896*Function::mk_monomial(0,1,0,2,2,0) + 160*Function::mk_monomial(0,1,0,2,2,1) - 
   16*Function::mk_monomial(0,1,0,2,3,0) - 2048*Function::mk_monomial(0,1,0,3,0,0) - 1152*Function::mk_monomial(0,1,0,3,0,1) + 
   384*Function::mk_monomial(0,1,0,3,1,0) + 128*Function::mk_monomial(0,1,0,3,1,1) + 64*Function::mk_monomial(0,1,0,3,2,0) - 
   8*Function::mk_monomial(0,1,0,3,2,1) + 384*Function::mk_monomial(0,1,0,4,0,0) - 48*Function::mk_monomial(0,1,0,4,1,0) - 
   4096*Function::mk_monomial(1,0,0,1,0,2) + 8192*Function::mk_monomial(1,0,0,1,1,1) - 4096*Function::mk_monomial(1,0,0,1,2,0) + 
   512*Function::mk_monomial(1,0,0,2,0,2) - 1024*Function::mk_monomial(1,0,0,2,1,1) + 512*Function::mk_monomial(1,0,0,2,2,0) + 
   4096*Function::mk_monomial(1,0,0,3,0,0) - 16*Function::mk_monomial(1,0,0,3,0,2) + 32*Function::mk_monomial(1,0,0,3,1,1) - 
16*Function::mk_monomial(1,0,0,3,2,0) - 512*Function::mk_monomial(1,0,0,4,0,0) + 16*Function::mk_monomial(1,0,0,5,0,0);

static const interval t25("25");
const Function Lib::num_combo1 = 
(512*Function::mk_monomial(0,0,1,0,0,3) - 1536*Function::mk_monomial(0,0,1,0,1,2) + 1536*Function::mk_monomial(0,0,1,0,2,1) - 
   512*Function::mk_monomial(0,0,1,0,3,0) - 2560*Function::mk_monomial(0,0,1,1,0,2) - 32*Function::mk_monomial(0,0,1,1,0,3) + 
   1024*Function::mk_monomial(0,0,1,1,1,1) + 416*Function::mk_monomial(0,0,1,1,1,2) + 1536*Function::mk_monomial(0,0,1,1,2,0) - 
   480*Function::mk_monomial(0,0,1,1,2,1) + 96*Function::mk_monomial(0,0,1,1,3,0) + 1536*Function::mk_monomial(0,0,1,2,0,1) + 
   224*Function::mk_monomial(0,0,1,2,0,2) + 4*Function::mk_monomial(0,0,1,2,0,3) - 1536*Function::mk_monomial(0,0,1,2,1,0) + 
   64*Function::mk_monomial(0,0,1,2,1,1) - 40*Function::mk_monomial(0,0,1,2,1,2) - 288*Function::mk_monomial(0,0,1,2,2,0) + 
   36*Function::mk_monomial(0,0,1,2,2,1) + 512*Function::mk_monomial(0,0,1,3,0,0) - 96*Function::mk_monomial(0,0,1,3,0,1) - 
   16*Function::mk_monomial(0,0,1,3,0,2) + 288*Function::mk_monomial(0,0,1,3,1,0) - 32*Function::mk_monomial(0,0,1,3,1,1) + 
   2*Function::mk_monomial(0,0,1,3,1,2) - 96*Function::mk_monomial(0,0,1,4,0,0) + 12*Function::mk_monomial(0,0,1,4,0,1) + 
   25600*Function::mk_monomial(0,0,2,0,0,2) - 51200*Function::mk_monomial(0,0,2,0,1,1) + 25600*Function::mk_monomial(0,0,2,0,2,0) + 
   51200*Function::mk_monomial(0,0,2,1,0,1) - 6400*Function::mk_monomial(0,0,2,1,0,2) - 51200*Function::mk_monomial(0,0,2,1,1,0) + 
   6400*Function::mk_monomial(0,0,2,1,1,1) + 25600*Function::mk_monomial(0,0,2,2,0,0) - 6400*Function::mk_monomial(0,0,2,2,0,1) + 
   400*Function::mk_monomial(0,0,2,2,0,2) - 512*Function::mk_monomial(0,1,0,0,0,3) + 1536*Function::mk_monomial(0,1,0,0,1,2) - 
   1536*Function::mk_monomial(0,1,0,0,2,1) + 512*Function::mk_monomial(0,1,0,0,3,0) + 1536*Function::mk_monomial(0,1,0,1,0,2) + 
   96*Function::mk_monomial(0,1,0,1,0,3) + 1024*Function::mk_monomial(0,1,0,1,1,1) - 480*Function::mk_monomial(0,1,0,1,1,2) - 
   2560*Function::mk_monomial(0,1,0,1,2,0) + 416*Function::mk_monomial(0,1,0,1,2,1) - 32*Function::mk_monomial(0,1,0,1,3,0) - 
   1536*Function::mk_monomial(0,1,0,2,0,1) - 288*Function::mk_monomial(0,1,0,2,0,2) + 1536*Function::mk_monomial(0,1,0,2,1,0) + 
   64*Function::mk_monomial(0,1,0,2,1,1) + 36*Function::mk_monomial(0,1,0,2,1,2) + 224*Function::mk_monomial(0,1,0,2,2,0) - 
   40*Function::mk_monomial(0,1,0,2,2,1) + 4*Function::mk_monomial(0,1,0,2,3,0) + 512*Function::mk_monomial(0,1,0,3,0,0) + 
   288*Function::mk_monomial(0,1,0,3,0,1) - 96*Function::mk_monomial(0,1,0,3,1,0) - 32*Function::mk_monomial(0,1,0,3,1,1) - 
   16*Function::mk_monomial(0,1,0,3,2,0) + 2*Function::mk_monomial(0,1,0,3,2,1) - 96*Function::mk_monomial(0,1,0,4,0,0) + 
   12*Function::mk_monomial(0,1,0,4,1,0) - 51200*Function::mk_monomial(0,1,1,0,0,2) + 102400*Function::mk_monomial(0,1,1,0,1,1) - 
   51200*Function::mk_monomial(0,1,1,0,2,0) + 6400*Function::mk_monomial(0,1,1,1,0,2) - 12800*Function::mk_monomial(0,1,1,1,1,1) + 
   6400*Function::mk_monomial(0,1,1,1,2,0) + 51200*Function::mk_monomial(0,1,1,2,0,0) - 6400*Function::mk_monomial(0,1,1,2,0,1) - 
   6400*Function::mk_monomial(0,1,1,2,1,0) + 800*Function::mk_monomial(0,1,1,2,1,1) + 25600*Function::mk_monomial(0,2,0,0,0,2) - 
   51200*Function::mk_monomial(0,2,0,0,1,1) + 25600*Function::mk_monomial(0,2,0,0,2,0) - 51200*Function::mk_monomial(0,2,0,1,0,1) + 
   51200*Function::mk_monomial(0,2,0,1,1,0) + 6400*Function::mk_monomial(0,2,0,1,1,1) - 6400*Function::mk_monomial(0,2,0,1,2,0) + 
   25600*Function::mk_monomial(0,2,0,2,0,0) - 6400*Function::mk_monomial(0,2,0,2,1,0) + 400*Function::mk_monomial(0,2,0,2,2,0) + 
   1024*Function::mk_monomial(1,0,0,1,0,2) - 2048*Function::mk_monomial(1,0,0,1,1,1) + 1024*Function::mk_monomial(1,0,0,1,2,0) - 
   128*Function::mk_monomial(1,0,0,2,0,2) + 256*Function::mk_monomial(1,0,0,2,1,1) - 128*Function::mk_monomial(1,0,0,2,2,0) - 
   1024*Function::mk_monomial(1,0,0,3,0,0) + 4*Function::mk_monomial(1,0,0,3,0,2) - 8*Function::mk_monomial(1,0,0,3,1,1) + 
   4*Function::mk_monomial(1,0,0,3,2,0) + 128*Function::mk_monomial(1,0,0,4,0,0) - 4*Function::mk_monomial(1,0,0,5,0,0) - 
   102400*Function::mk_monomial(1,0,1,1,0,1) + 102400*Function::mk_monomial(1,0,1,1,1,0) - 
   102400*Function::mk_monomial(1,0,1,2,0,0) + 19200*Function::mk_monomial(1,0,1,2,0,1) - 6400*Function::mk_monomial(1,0,1,2,1,0) + 
   6400*Function::mk_monomial(1,0,1,3,0,0) - 800*Function::mk_monomial(1,0,1,3,0,1) + 102400*Function::mk_monomial(1,1,0,1,0,1) - 
   102400*Function::mk_monomial(1,1,0,1,1,0) - 102400*Function::mk_monomial(1,1,0,2,0,0) - 6400*Function::mk_monomial(1,1,0,2,0,1) + 
   19200*Function::mk_monomial(1,1,0,2,1,0) + 6400*Function::mk_monomial(1,1,0,3,0,0) - 800*Function::mk_monomial(1,1,0,3,1,0) + 
 102400*Function::mk_monomial(2,0,0,2,0,0) - 12800*Function::mk_monomial(2,0,0,3,0,0) + 400*Function::mk_monomial(2,0,0,4,0,0))*(L::one/t25);


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
  //cout << "tested " << s << endl << flush;
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
  Function y2 =  (Function::compose(Lib::y1,(Lib::x2),(Lib::x3),(Lib::x1),(Lib::x5),(Lib::x6),(Lib::x4)));
  epsValue("y2",y2,sqrt(4.2));

  /* i_flat_term_x */ {
  Function f = Lib::promote1_to_6(Lib::i_flat_term_x);
  epsValue("i_flat_term",f,0.00201859856768314477);
  }


  /* gamma2_x_div_azim_v2 */ {
    /*
    univariate f1 =  Lib::i_gamma2_x_div_azim_v2(interval::interval("1.1"));
  Function f = Lib::promote1_to_6(f1);
  epsValue("gamma2_x_div_azim_v2",f,0.102244026021654014);
  Function g = (Lib::uni(f1 , (Lib::x1)));
  epsValue("test gamma2",g,0.102244026021654014);
    */
    // value computed in Mathematica with gamma2Ldivalpha[Sqrt[6.36]/2] function.
    /* test1 */ {
    univariate f1 =  Lib::i_gamma2_x_div_azim_v2(interval::interval("0.0"));
  Function f = Lib::promote1_to_6(f1);
  epsValue("gamma2_x_div_azim_v2",f,0.0326792785715012028653739253059);
  Function g = (Lib::uni(f1 , (Lib::x1)));
  epsValue("test gamma2",g,0.0326792785715012028653739253059);
    }


  }

  /* truncate_dih_x  {
    Function f = Lib::truncate_dih_x(interval::interval("0.14"));
    Function g = Lib::dih_x;
    domain d(6.36,4.2,4.3,4.4,4.5,4.6);
    double x = g.evalf(d,d).upperBound();
    epsValue("truncate_dih_x",Lib::truncate_dih_x(interval::interval("0.14")),x);
    } */

  /* truncate vol_x  {
    Function f = uni(L::i_sqrt,Lib::delta_x) * (one/twelve);
    Function g = Lib::truncate_vol_x(interval::interval("0.14"));
    domain d(6.36,4.2,4.3,4.4,4.5,4.6);
    double x = f.evalf(d,d).upperBound();
    epsValue("truncate_vol_x",g,x);
  }
  */

  cout << " -- done loading LibA" << endl << flush;

}
