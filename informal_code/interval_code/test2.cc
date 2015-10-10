#include "error.h"
#include <float.h>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string.h>
#include "interval.h"
#include "lineInterval.h"
#include "univariate.h"
#include "wide.h"
#include "secondDerive.h"
#include "taylorData.h"
#include "Lib.h"
#include "recurse.h"
#include <time.h>
#include <string.h>
#include <stdlib.h>

using namespace std;

// This one we have to compute externally.
static const interval hminus("1.2317544220903043901");

static bool epsilonCloseDoubles(const char* s, double x,double y,double epsilon)
{
  if (abs(y-x)>epsilon * (0.1+abs(x)+abs(y)))
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
  //cout << "-- tested " << s << endl << flush;
}

/*
static void uniValue(const char* s,const univariate& u,double x) {
  double eps = 1.0e-8;
  interval i("1.1");
  double y = u.eval(i,0).hi;
  epsilonCloseDoubles(s,x,y,eps);
}
*/

void moduleTest()
	{
	interMath::selfTest();
	linearization::selfTest();
	univariate::selfTest();
	wide::selfTest();
	secondDerive::selfTest();
	Function::selfTest();
	Lib::selfTest();
	}

// Warning: pi computed by floating point
static const interval pi ("3.14159265358979311600");
// Warning: cos797 computed by floating point
static const interval cos797 ("0.69885563921392235276");
// Warning: h0 computed by floating point
static const interval h0 ("1.26000000000000000888");
// Warning: hplus computed by floating point
static const interval hplus ("1.32539999999999991154");
// Warning: sqrt3 computed by floating point
static const interval sqrt3 ("1.73205080756887719318");
// Warning: sqrt8 computed by floating point
static const interval sqrt8 ("2.82842712474619029095");
// Warning: sol0 computed by floating point
static const interval sol0 ("0.55128559843253110984");
// Warning: tau0 computed by floating point
static const interval tau0 ("1.54065864570855026727");
// Warning: mm1 computed by floating point
static const interval mm1 ("1.01208086842065947408");
// Warning: mm2 computed by floating point
static const interval mm2 ("0.02541450726950933436");
// Warning: rh0 computed by floating point
static const interval rh0 ("3.84615384615384581224");
// Warning: const1 computed by floating point
static const interval const1 ("0.17547965609182192281");
// Warning: arc_hhn computed by floating point
static const interval arc_hhn ("0.81611135460255679330");static const Function rotate2(const Function& f) {
     return (Function::compose(f,(Lib::x2),(Lib::x3),(Lib::x1),(Lib::x5),(Lib::x6),(Lib::x4)));
  }

static const Function rotate3(const Function& f) {
     return (Function::compose(f,(Lib::x3),(Lib::x1),(Lib::x2),(Lib::x6),(Lib::x4),(Lib::x5)));
  }

static const Function rotate4(const Function& f) {
     return (Function::compose(f,(Lib::x4),(Lib::x2),(Lib::x6),(Lib::x1),(Lib::x5),(Lib::x3)));
  }

static const Function rotate5(const Function& f) {
     return (Function::compose(f,(Lib::x5),(Lib::x3),(Lib::x4),(Lib::x2),(Lib::x6),(Lib::x1)));
  }

static const Function rotate6(const Function& f) {
     return (Function::compose(f,(Lib::x6),(Lib::x1),(Lib::x5),(Lib::x3),(Lib::x4),(Lib::x2)));
  }

static const Function mk_126(const Function& f) {
     return (Function::compose(f,(Lib::x1),(Lib::x2),(Lib::two6),(Lib::two6),(Lib::two6),(Lib::x6)));
  }

static const Function mk_135(const Function& f) {
     return (Function::compose(f,(Lib::x1),(Lib::two6),(Lib::x3),(Lib::two6),(Lib::x5),(Lib::two6)));
  }

static const Function mk_456(const Function& f) {
     return (Function::compose(f,(Lib::two6),(Lib::two6),(Lib::two6),(Lib::x4),(Lib::x5),(Lib::x6)));
  }

static const Function rotate234(const Function& f) {
     return (Function::compose(f,(Lib::x2),(Lib::x3),(Lib::x4),(Lib::unit),(Lib::unit),(Lib::unit)));
  }

static const Function rotate126(const Function& f) {
     return (Function::compose(f,(Lib::x1),(Lib::x2),(Lib::x6),(Lib::unit),(Lib::unit),(Lib::unit)));
  }

static const Function rotate345(const Function& f) {
     return (Function::compose(f,(Lib::x3),(Lib::x4),(Lib::x5),(Lib::unit),(Lib::unit),(Lib::unit)));
  }
static const Function proj_y2 = (rotate2((Lib::y1)));

static const Function proj_y3 = (rotate3((Lib::y1)));

static const Function proj_y4 = (rotate4((Lib::y1)));

static const Function proj_y5 = (rotate5((Lib::y1)));

static const Function proj_y6 = (rotate6((Lib::y1)));

static const Function zero6 = (Lib::constant6(interval("0.")));

static const Function four6 = (Lib::constant6(interval("4.")));

static const Function dummy6 = (Lib::constant6(interval("0.")));

static const Function x1cube = ((Lib::x1) * ((Lib::x1) * (Lib::x1)));

static const Function norm2hh_x = ((Lib::uni((univariate::i_pow2) , ((Lib::y1) - (Lib::constant6(((hminus) + (hplus))))))) + ((Lib::uni((univariate::i_pow2) , ((proj_y2) - (Lib::two6)))) + ((Lib::uni((univariate::i_pow2) , ((proj_y3) - (Lib::two6)))) + ((Lib::uni((univariate::i_pow2) , ((proj_y4) - (Lib::two6)))) + ((Lib::uni((univariate::i_pow2) , ((proj_y5) - (Lib::two6)))) + (Lib::uni((univariate::i_pow2) , ((proj_y6) - (Lib::two6)))))))));

static const Function x1_delta_x = ((Lib::x1) * (Lib::delta_x));

static const Function delta4_squared_x = (Lib::uni((univariate::i_pow2) , (Lib::delta_x4)));

static const Function vol_x = ((Lib::uni((univariate::i_sqrt) , (Lib::delta_x))) * (interval("1.") / interval("12.")));

static const Function dih2_x = (rotate2((Lib::dih_x)));

static const Function dih3_x = (rotate3((Lib::dih_x)));

static const Function dih4_x = (rotate4((Lib::dih_x)));

static const Function dih5_x = (rotate5((Lib::dih_x)));

static const Function dih6_x = (rotate6((Lib::dih_x)));

static const Function lfun_y1 = ((((Lib::unit) * (h0)) - (Lib::x1)) * (rh0));

static const Function ldih_x = (((((Lib::unit) * (h0)) - ((Lib::y1) * interval("0.5"))) * (rh0)) * (Lib::dih_x));

static const Function ldih2_x = (rotate2((ldih_x)));

static const Function ldih3_x = (rotate3((ldih_x)));

static const Function ldih6_x = (rotate6((ldih_x)));

static const Function eulerA_x = (((Lib::y1) * ((proj_y2) * (proj_y3))) + ((((Lib::y1) * ((Lib::x2) + ((Lib::x3) - (Lib::x4)))) * interval("0.5")) + ((((proj_y2) * ((Lib::x1) + ((Lib::x3) - (Lib::x5)))) * interval("0.5")) + (((proj_y3) * ((Lib::x1) + ((Lib::x2) - (Lib::x6)))) * interval("0.5")))));

static const Function gchi1_x = ((Lib::uni((Lib::i_gchi) , (Lib::y1))) * (Lib::dih_x));

static const Function gchi2_x = ((Lib::uni((Lib::i_gchi) , (proj_y2))) * (dih2_x));

static const Function gchi3_x = ((Lib::uni((Lib::i_gchi) , (proj_y3))) * (dih3_x));

static const Function gchi4_x = ((Lib::uni((Lib::i_gchi) , (proj_y4))) * (dih4_x));

static const Function gchi5_x = ((Lib::uni((Lib::i_gchi) , (proj_y5))) * (dih5_x));

static const Function gchi6_x = ((Lib::uni((Lib::i_gchi) , (proj_y6))) * (dih6_x));

static const Function halfbump_x4 = (rotate4((Lib::halfbump_x1)));

static const Function eta2_135 = (rotate3((Lib::eta2_126)));

static const Function eta2_456 = (rotate4((eta2_135)));

static const Function vol3_x_sqrt = (mk_126((vol_x)));

static const Function vol3f_x_lfun = (((Lib::constant6((interval("2.") * ((mm1) / (pi))))) * (((Lib::two6) * (mk_126((Lib::dih_x)))) + (((Lib::two6) * (mk_126((dih2_x)))) + (((Lib::two6) * (mk_126((dih6_x)))) + ((mk_126((dih3_x))) + ((mk_126((dih4_x))) + ((mk_126((dih5_x))) - (Lib::constant6((interval("3.") * (pi))))))))))) - ((Lib::constant6((interval("8.") * ((mm2) / (pi))))) * ((mk_126((ldih_x))) + ((mk_126((ldih2_x))) + (mk_126((ldih6_x)))))));

static const Function vol3f_x_sqrt2_lmplus = (((Lib::constant6((interval("2.") * ((mm1) / (pi))))) * (((Lib::two6) * (mk_126((Lib::dih_x)))) + (((Lib::two6) * (mk_126((dih2_x)))) + (((Lib::two6) * (mk_126((dih6_x)))) + ((mk_126((dih3_x))) + ((mk_126((dih4_x))) + ((mk_126((dih5_x))) - (Lib::constant6((interval("3.") * (pi))))))))))) - ((Lib::constant6((interval("8.") * ((mm2) / (pi))))) * ((mk_126((ldih2_x))) + (mk_126((ldih6_x))))));

static const Function asn797k = ((Lib::x1) * (Lib::uni((univariate::i_asin) , ((Lib::constant6((cos797))) * (Lib::uni((univariate::i_sin) , ((Lib::constant6((pi))) / (Lib::x1))))))));

static const Function asnFnhk = ((Lib::x2) * (Lib::uni((univariate::i_asin) , ((((Lib::x1) * (Lib::constant6(((sqrt3) / interval("4."))))) + ((Lib::uni((univariate::i_sqrt) , ((Lib::unit) - (Lib::uni((univariate::i_pow2) , ((Lib::x1) * (Lib::constant6(interval("0.5"))))))))) * (Lib::constant6(interval("0.5"))))) * (Lib::uni((univariate::i_sin) , ((Lib::constant6((pi))) / (Lib::x2))))))));

static const Function acs_sqrt_x1_d4 = (Lib::uni((univariate::i_acos) , ((Lib::y1) * interval("0.25"))));

static const Function acs_sqrt_x2_d4 = (Lib::uni((univariate::i_acos) , ((proj_y2) * interval("0.25"))));

static const Function arclength_x_123 = (Lib::uni((univariate::i_acos) , (((Lib::x1) + ((Lib::x2) - (Lib::x3))) / (Lib::uni((univariate::i_sqrt) , (((Lib::x1) * (Lib::x2)) * interval("4.")))))));

static const Function arclength_x_234 = (rotate234((arclength_x_123)));

static const Function arclength_x_126 = (rotate126((arclength_x_123)));

static const Function sol_euler_x_div_sqrtdelta = ((Lib::uni((univariate::i_matan) , ((Lib::delta_x) / (((eulerA_x) * (eulerA_x)) * interval("4."))))) / (eulerA_x));

static const Function sol_euler246_x_div_sqrtdelta = (rotate4((sol_euler_x_div_sqrtdelta)));

static const Function sol_euler345_x_div_sqrtdelta = (rotate5((sol_euler_x_div_sqrtdelta)));

static const Function sol_euler156_x_div_sqrtdelta = (rotate6((sol_euler_x_div_sqrtdelta)));

static const Function dih_x_div_sqrtdelta_posbranch = ((((Lib::y1) * interval("2.")) / (Lib::delta_x4)) * (Lib::uni((univariate::i_matan) , ((((Lib::x1) * (Lib::delta_x)) * interval("4.")) / (Lib::uni((univariate::i_pow2) , (Lib::delta_x4)))))));

static const Function dih3_x_div_sqrtdelta_posbranch = (rotate3((dih_x_div_sqrtdelta_posbranch)));

static const Function dih4_x_div_sqrtdelta_posbranch = (rotate4((dih_x_div_sqrtdelta_posbranch)));

static const Function dih5_x_div_sqrtdelta_posbranch = (rotate5((dih_x_div_sqrtdelta_posbranch)));

static const Function dih_x_126_s2 = (mk_126((Lib::dih_x)));

static const Function dih2_x_126_s2 = (mk_126((dih2_x)));

static const Function dih3_x_126_s2 = (mk_126((dih3_x)));

static const Function dih4_x_126_s2 = (mk_126((dih4_x)));

static const Function dih5_x_126_s2 = (mk_126((dih5_x)));

static const Function dih6_x_126_s2 = (mk_126((dih6_x)));

static const Function dih_x_135_s2 = (mk_135((Lib::dih_x)));

static const Function dih2_x_135_s2 = (mk_135((dih2_x)));

static const Function dih3_x_135_s2 = (mk_135((dih3_x)));

static const Function dih4_x_135_s2 = (mk_135((dih4_x)));

static const Function dih5_x_135_s2 = (mk_135((dih5_x)));

static const Function dih6_x_135_s2 = (mk_135((dih6_x)));

static const Function ldih_x_126_s2 = ((Lib::uni((Lib::i_lfun) , ((Lib::y1) / (Lib::two6)))) * (dih_x_126_s2));

static const Function ldih2_x_126_s2 = ((Lib::uni((Lib::i_lfun) , ((proj_y2) / (Lib::two6)))) * (dih2_x_126_s2));

static const Function ldih6_x_126_s2 = ((Lib::uni((Lib::i_lfun) , ((proj_y6) / (Lib::two6)))) * (dih6_x_126_s2));

static const Function ldih_x_135_s2 = ((Lib::uni((Lib::i_lfun) , ((Lib::y1) / (Lib::two6)))) * (dih_x_135_s2));

static const Function ldih3_x_135_s2 = ((Lib::uni((Lib::i_lfun) , ((proj_y3) / (Lib::two6)))) * (dih3_x_135_s2));

static const Function ldih5_x_135_s2 = ((Lib::uni((Lib::i_lfun) , ((proj_y5) / (Lib::two6)))) * (dih5_x_135_s2));

static const Function euler_3flat_x = (Function::compose((eulerA_x),(Lib::x1),(Lib::x2),(Lib::x3),(Function::compose((Lib::edge_flat2_x),(Lib::x4),(Lib::x2),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x5),(Lib::x1),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6)))));

static const Function euler_2flat_x = (Function::compose((eulerA_x),(Lib::x1),(Lib::x2),(Lib::x3),(Lib::x4),(Function::compose((Lib::edge_flat2_x),(Lib::x5),(Lib::x1),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6)))));

static const Function euler_1flat_x = (Function::compose((eulerA_x),(Lib::x1),(Lib::x2),(Lib::x3),(Lib::x4),(Lib::x5),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6)))));

static const Function rhazim_x = ((Lib::uni((Lib::i_rho) , (Lib::y1))) * (Lib::dih_x));

static const Function rhazim2_x = (rotate2((rhazim_x)));

static const Function rhazim3_x = (rotate3((rhazim_x)));

static const Function taum_x = ((rhazim_x) + ((rhazim2_x) + ((rhazim3_x) - (Lib::constant6(((interval("1.") + (const1)) * (pi)))))));

static const Function taum_3flat_x = ((Function::compose((taum_x),(Lib::x1),(Lib::x2),(Lib::x3),(Function::compose((Lib::edge_flat2_x),(Lib::x4),(Lib::x2),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x5),(Lib::x1),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6))))) + ((Lib::uni((Lib::i_flat_term_x) , (Lib::x4))) + ((Lib::uni((Lib::i_flat_term_x) , (Lib::x5))) + (Lib::uni((Lib::i_flat_term_x) , (Lib::x6))))));

static const Function taum_2flat_x = ((Function::compose((taum_x),(Lib::x1),(Lib::x2),(Lib::x3),(Lib::x4),(Function::compose((Lib::edge_flat2_x),(Lib::x5),(Lib::x1),(Lib::x3),(zero6),(four6),(four6))),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6))))) + ((Lib::uni((Lib::i_flat_term_x) , (Lib::x5))) + (Lib::uni((Lib::i_flat_term_x) , (Lib::x6)))));

static const Function taum_1flat_x = ((Function::compose((taum_x),(Lib::x1),(Lib::x2),(Lib::x3),(Lib::x4),(Lib::x5),(Function::compose((Lib::edge_flat2_x),(Lib::x6),(Lib::x1),(Lib::x2),(zero6),(four6),(four6))))) + (Lib::uni((Lib::i_flat_term_x) , (Lib::x6))));

static const Function delta_x_126_s2 = (mk_126((Lib::delta_x)));

static const Function delta_x_135_s2 = (mk_135((Lib::delta_x)));

static const Function delta_pent_x = (Function::compose((Lib::delta_x),(Lib::x1),(Lib::x2),(Lib::x6),(four6),(four6),(Lib::constant6(interval("10.4976")))));

static const Function vol3_x_135_s2 = (mk_135((vol_x)));

static const Function ldih_x_div_sqrtdelta_posbranch = ((((Lib::constant6((h0))) - ((Lib::y1) * interval("0.5"))) * (rh0)) * (dih_x_div_sqrtdelta_posbranch));

static const Function ldih2_x_div_sqrtdelta_posbranch = (rotate2((ldih_x_div_sqrtdelta_posbranch)));

static const Function ldih3_x_div_sqrtdelta_posbranch = (rotate3((ldih_x_div_sqrtdelta_posbranch)));

static const Function ldih5_x_div_sqrtdelta_posbranch = (rotate5((ldih_x_div_sqrtdelta_posbranch)));

static const Function ldih6_x_div_sqrtdelta_posbranch = (rotate6((ldih_x_div_sqrtdelta_posbranch)));

static const Function ldih_x_n = ((Lib::uni((univariate::i_sqn) , (Lib::delta_x))) * (ldih_x_div_sqrtdelta_posbranch));

static const Function ldih_x_126_n = (mk_126((ldih_x_n)));

static const Function ldih2_x_126_n = (mk_126((rotate2((ldih_x_n)))));

static const Function ldih6_x_126_n = (mk_126((rotate6((ldih_x_n)))));

static const Function ldih_x_135_n = (mk_135((ldih_x_n)));

static const Function ldih3_x_135_n = (mk_135((rotate3((ldih_x_n)))));

static const Function ldih5_x_135_n = (mk_135((rotate5((ldih_x_n)))));

static const Function rhazim_x_div_sqrtdelta_posbranch = ((Lib::uni((Lib::i_rho) , (Lib::y1))) * (dih_x_div_sqrtdelta_posbranch));

static const Function rhazim2_x_div_sqrtdelta_posbranch = (rotate2((rhazim_x_div_sqrtdelta_posbranch)));

static const Function rhazim3_x_div_sqrtdelta_posbranch = (rotate3((rhazim_x_div_sqrtdelta_posbranch)));

static const Function tau_residual_x = ((rhazim_x_div_sqrtdelta_posbranch) + ((rhazim2_x_div_sqrtdelta_posbranch) + (rhazim3_x_div_sqrtdelta_posbranch)));

static const Function dnum1 = ((((Lib::constant6(interval("16."))) - ((Lib::constant6(interval("2."))) * (Lib::x4))) * (Lib::x1)) + ((((Lib::x5) - (Lib::constant6(interval("8.")))) * (Lib::x2)) + (((Lib::x6) - (Lib::constant6(interval("8.")))) * (Lib::x3))));

static const Function delta_x1 = (rotate4((Lib::delta_x4)));

static const Function mu6_x = ((Lib::constant6(interval("0.012"))) + (((Lib::constant6(interval("0.07"))) * ((Lib::constant6(interval("2.52"))) - (Lib::y1))) + ((Lib::constant6(interval("0.01"))) * (((Lib::constant6((interval("2.52") * interval("2.")))) - (proj_y2)) - (proj_y3)))));

static const Function taud_x = ((Lib::promote1_to_6((Lib::i_flat_term_x))) + ((Lib::uni((univariate::i_sqrt) , (Lib::delta_x))) * (mu6_x)));

static const Function taud_D2_num_x = ((((Lib::constant6((-interval("0.07")))) * ((Lib::delta_x) * ((delta_x1) * ((Lib::constant6(interval("2."))) * (Lib::y1))))) - ((Lib::constant6((interval("1.") / interval("4.")))) * ((mu6_x) * (((delta_x1) * ((Lib::constant6(interval("2."))) * (Lib::y1))) * ((delta_x1) * ((Lib::constant6(interval("2."))) * (Lib::y1))))))) + ((Lib::constant6((interval("1.") / interval("2.")))) * ((mu6_x) * ((Lib::delta_x) * (((Lib::constant6((-interval("8.")))) * ((Lib::x1) * (Lib::x4))) + ((delta_x1) * (Lib::constant6(interval("2.")))))))));

static const Function taud_D1_num_x = (((Lib::constant6((-interval("0.07")))) * (Lib::delta_x)) + (((Lib::constant6((interval("1.") / interval("2.")))) * ((mu6_x) * ((delta_x1) * ((Lib::constant6(interval("2."))) * (Lib::y1))))) + ((Lib::constant6(((sol0) / interval("0.52")))) * (Lib::uni((univariate::i_sqrt) , (Lib::delta_x))))));
static const Function taum_x1(const interval& a,const interval& b) { return ((Function::compose((taum_x),(four6),(four6),(four6),(Lib::constant6((a * a))),(Lib::constant6((b * b))),(Lib::x1)))); }

static const Function taum_x2(const interval& a,const interval& b) { return ((Function::compose((taum_x),(four6),(four6),(four6),(Lib::constant6((a * a))),(Lib::constant6((b * b))),(Lib::x2)))); }

static const Function taum_x1_x2(const interval& a) { return ((Function::compose((taum_x),(four6),(four6),(four6),(Lib::constant6((a * a))),(Lib::x1),(Lib::x2)))); }

static const Function arclength_x1(const interval& a,const interval& b) { return ((Function::compose((arclength_x_123),(Lib::x1),(Lib::constant6((a * a))),(Lib::constant6((b * b))),(dummy6),(dummy6),(dummy6)))); }

static const Function arclength_x2(const interval& a,const interval& b) { return ((Function::compose((arclength_x_123),(Lib::x2),(Lib::constant6((a * a))),(Lib::constant6((b * b))),(dummy6),(dummy6),(dummy6)))); }

static const Function delta_126_x(const interval& a,const interval& b,const interval& c) { return ((Function::compose((Lib::delta_x),(Lib::x1),(Lib::x2),(Lib::constant6(a)),(Lib::constant6(b)),(Lib::constant6(c)),(Lib::x6)))); }

static const Function delta_234_x(const interval& a,const interval& b,const interval& c) { return ((Function::compose((Lib::delta_x),(Lib::constant6(a)),(Lib::x2),(Lib::x3),(Lib::x4),(Lib::constant6(b)),(Lib::constant6(c))))); }

static const Function delta_135_x(const interval& a,const interval& b,const interval& c) { return ((Function::compose((Lib::delta_x),(Lib::x1),(Lib::constant6(a)),(Lib::x3),(Lib::constant6(b)),(Lib::x5),(Lib::constant6(c))))); }

static const Function delta_sub1_x(const interval& a) { return ((Function::compose((Lib::delta_x),(Lib::constant6(a)),(Lib::x2),(Lib::x3),(Lib::x4),(Lib::x5),(Lib::x6)))); }

static const Function taum_sub1_x(const interval& a) { return ((Function::compose((taum_x),(Lib::constant6(a)),(Lib::x2),(Lib::x3),(Lib::x4),(Lib::x5),(Lib::x6)))); }

static const Function taum_sub246_x(const interval& a,const interval& b,const interval& c) { return ((Function::compose((taum_x),(Lib::x1),(Lib::constant6(a)),(Lib::x3),(Lib::constant6(b)),(Lib::x5),(Lib::constant6(c))))); }

static const Function taum_sub345_x(const interval& a,const interval& b,const interval& c) { return ((Function::compose((taum_x),(Lib::x1),(Lib::x2),(Lib::constant6(a)),(Lib::constant6(b)),(Lib::constant6(c)),(Lib::x6)))); }

static const Function gamma2_x1_div_a_v2(const interval& m) { return ((Lib::promote1_to_6((Lib::i_gamma2_x_div_azim_v2(m))))); }

static const Function gamma3f_x_div_sqrtdelta(const interval& m4,const interval& m5,const interval& m6) { return (((Lib::constant6((interval("1.") / interval("12.")))) - ((((mk_456((rotate5((sol_euler_x_div_sqrtdelta))))) + ((mk_456((rotate6((sol_euler_x_div_sqrtdelta))))) + (mk_456((rotate4((sol_euler_x_div_sqrtdelta))))))) * (interval("2.") * ((mm1) / (pi)))) - ((((Lib::uni((Lib::i_lfun) , ((proj_y4) * interval("0.5")))) * ((mk_456((rotate4((dih_x_div_sqrtdelta_posbranch))))) * m4)) + (((Lib::uni((Lib::i_lfun) , ((proj_y5) * interval("0.5")))) * ((mk_456((rotate5((dih_x_div_sqrtdelta_posbranch))))) * m5)) + ((Lib::uni((Lib::i_lfun) , ((proj_y6) * interval("0.5")))) * ((mk_456((rotate6((dih_x_div_sqrtdelta_posbranch))))) * m6)))) * (interval("8.") * ((mm2) / (pi))))))); }

static const Function vol3f_456(const interval& m4) { return (((((mk_456((rotate5((Lib::sol_x))))) + ((mk_456((rotate6((Lib::sol_x))))) + (mk_456((rotate4((Lib::sol_x))))))) * (interval("2.") * ((mm1) / (pi)))) - (((((Lib::uni((Lib::i_lfun) , ((proj_y4) * interval("0.5")))) * m4) * (mk_456((rotate4((Lib::dih_x)))))) + (((Lib::uni((Lib::i_lfun) , ((proj_y5) * interval("0.5")))) * (mk_456((rotate5((Lib::dih_x)))))) + ((Lib::uni((Lib::i_lfun) , ((proj_y6) * interval("0.5")))) * (mk_456((rotate6((Lib::dih_x)))))))) * (interval("8.") * ((mm2) / (pi)))))); }

static const Function gamma3_x(const interval& m4) { return (((mk_456((vol_x))) - (vol3f_456(m4)))); }

static const Function gamma23_full8_x(const interval& m1) { return (((Function::compose((gamma3_x(m1)),(dummy6),(dummy6),(dummy6),(Lib::x1),(Lib::x2),(Lib::x6))) + ((Function::compose((gamma3_x(m1)),(dummy6),(dummy6),(dummy6),(Lib::x1),(Lib::x3),(Lib::x5))) + (((Lib::dih_x) - ((mk_126((Lib::dih_x))) + (mk_135((Lib::dih_x))))) * interval("0.008"))))); }

static const Function gamma23_keep135_x(const interval& m1) { return (((Function::compose((gamma3_x(m1)),(dummy6),(dummy6),(dummy6),(Lib::x1),(Lib::x3),(Lib::x5))) + (((Lib::dih_x) - (mk_135((Lib::dih_x)))) * interval("0.008")))); }

static const Function mud_135_x_v1(const interval& y2,const interval& y4,const interval& y6) { return (((Function::compose((mu6_x),(Lib::constant6((y2 * y2))),(Lib::x1),(Lib::x3),(dummy6),(dummy6),(dummy6))) * (Lib::uni((univariate::i_sqrt) , (delta_135_x((y2 * y2),(y4 * y4),(y6 * y6))))))); }

static const Function mud_126_x_v1(const interval& y3,const interval& y4,const interval& y5) { return (((Function::compose((mu6_x),(Lib::constant6((y3 * y3))),(Lib::x1),(Lib::x2),(dummy6),(dummy6),(dummy6))) * (Lib::uni((univariate::i_sqrt) , (delta_126_x((y3 * y3),(y4 * y4),(y5 * y5))))))); }

static const Function mud_234_x_v1(const interval& y1,const interval& y5,const interval& y6) { return (((Function::compose((mu6_x),(Lib::constant6((y1 * y1))),(Lib::x2),(Lib::x3),(dummy6),(dummy6),(dummy6))) * (Lib::uni((univariate::i_sqrt) , (delta_234_x((y1 * y1),(y5 * y5),(y6 * y6))))))); }

static const Function mudLs_234_x(const interval& d1s,const interval& d2s,const interval& y1,const interval& y5,const interval& y6) { return (((Function::compose((mu6_x),(Lib::constant6((y1 * y1))),(Lib::x2),(Lib::x3),(dummy6),(dummy6),(dummy6))) * (((Lib::constant6((interval("1.") / (d1s + d2s)))) * ((delta_234_x((y1 * y1),(y5 * y5),(y6 * y6))) - (Lib::constant6((d1s * d1s))))) + (Lib::constant6(d1s))))); }

static const Function mudLs_126_x(const interval& d1s,const interval& d2s,const interval& y3,const interval& y4,const interval& y5) { return (((Function::compose((mu6_x),(Lib::constant6((y3 * y3))),(Lib::x1),(Lib::x2),(dummy6),(dummy6),(dummy6))) * (((Lib::constant6((interval("1.") / (d1s + d2s)))) * ((delta_126_x((y3 * y3),(y4 * y4),(y5 * y5))) - (Lib::constant6((d1s * d1s))))) + (Lib::constant6(d1s))))); }

static const Function mudLs_135_x(const interval& d1s,const interval& d2s,const interval& y2,const interval& y4,const interval& y6) { return (((Function::compose((mu6_x),(Lib::constant6((y2 * y2))),(Lib::x1),(Lib::x3),(dummy6),(dummy6),(dummy6))) * (((Lib::constant6((interval("1.") / (d1s + d2s)))) * ((delta_135_x((y2 * y2),(y4 * y4),(y6 * y6))) - (Lib::constant6((d1s * d1s))))) + (Lib::constant6(d1s))))); }

static const Function edge2_126_x(const interval& d,const interval& x4,const interval& x5) { return ((((Lib::uni((univariate::i_sqrt) , (((Function::compose((Lib::ups_126),(Lib::constant6(x4)),(Lib::constant6(x5)),(dummy6),(dummy6),(dummy6),(Lib::x6))) * (Lib::ups_126)) + ((Lib::constant6(((-interval("4.")) * d))) * (Lib::x6))))) - ((Lib::constant6((-interval("1.")))) * (Function::compose((delta_x1),(zero6),(Lib::x2),(Lib::x1),(Lib::x6),(Lib::constant6(x5)),(Lib::constant6(x4)))))) / ((Lib::constant6(interval("2."))) * (Lib::x6)))); }

static const Function edge2_135_x(const interval& d,const interval& x4,const interval& x6) { return ((Function::compose((edge2_126_x(d,x4,x6)),(Lib::x1),(Lib::x3),(dummy6),(dummy6),(dummy6),(Lib::x5)))); }

static const Function edge2_234_x(const interval& d,const interval& x5,const interval& x6) { return ((Function::compose((edge2_126_x(d,x5,x6)),(Lib::x2),(Lib::x3),(dummy6),(dummy6),(dummy6),(Lib::x4)))); }

static const Function flat_term2_126_x(const interval& d,const interval& x4,const interval& x5) { return ((Lib::uni((Lib::i_flat_term_x) , (edge2_126_x(d,x4,x5))))); }

static const Function flat_term2_135_x(const interval& d,const interval& x4,const interval& x6) { return ((Lib::uni((Lib::i_flat_term_x) , (edge2_135_x(d,x4,x6))))); }

static const Function flat_term2_234_x(const interval& d,const interval& x5,const interval& x6) { return ((Lib::uni((Lib::i_flat_term_x) , (edge2_234_x(d,x5,x6))))); }

void selfTest() { 
       cout << " -- loading test_auto test" << endl << flush;
 
         epsValue("unit6",Lib::unit,1.000000000000);
  epsValue("proj_x1",Lib::x1,6.360000000000);
  epsValue("proj_x2",Lib::x2,4.200000000000);
  epsValue("proj_x3",Lib::x3,4.300000000000);
  epsValue("proj_x4",Lib::x4,4.400000000000);
  epsValue("proj_x5",Lib::x5,4.500000000000);
  epsValue("proj_x6",Lib::x6,4.600000000000);
  epsValue("proj_y1",Lib::y1,2.521904042584);
  epsValue("proj_y2",proj_y2,2.049390153192);
  epsValue("proj_y3",proj_y3,2.073644135333);
  epsValue("proj_y4",proj_y4,2.097617696340);
  epsValue("proj_y5",proj_y5,2.121320343560);
  epsValue("proj_y6",proj_y6,2.144761058953);
  epsValue("delta_x",Lib::delta_x,190.946160000000);
  epsValue("delta_x4",Lib::delta_x4,15.438400000000);
  epsValue("dih_x",Lib::dih_x,1.352808652107);
  epsValue("sol_x",Lib::sol_x,0.477631403144);
  epsValue("rad2_x",Lib::rad2_x,1.808053620979);
  epsValue("two6",Lib::two6,2.000000000000);
  epsValue("zero6",zero6,0.000000000000);
  epsValue("four6",four6,4.000000000000);
  epsValue("dummy6",dummy6,0.000000000000);
  epsValue("x1cube",x1cube,257.259456000000);
  epsValue("norm2hh_x",norm2hh_x,0.054309039746);
  epsValue("eta2_126",Lib::eta2_126,1.722716974360);
  epsValue("x1_delta_x",x1_delta_x,1214.417577600000);
  epsValue("delta4_squared_x",delta4_squared_x,238.344194560000);
  epsValue("vol_x",vol_x,1.151527246747);
  epsValue("dih2_x",dih2_x,1.121532564507);
  epsValue("dih3_x",dih3_x,1.144882840119);
  epsValue("dih4_x",dih4_x,1.534208237895);
  epsValue("dih5_x",dih5_x,1.097711268093);
  epsValue("dih6_x",dih6_x,1.121516296474);
  epsValue("lfun_y1",lfun_y1,-19.615384615385);
  epsValue("ldih_x",ldih_x,-0.004953471695);
  epsValue("ldih2_x",ldih2_x,1.015008208410);
  epsValue("ldih3_x",ldih3_x,0.982740711623);
  epsValue("ldih6_x",ldih6_x,0.809301129723);
  epsValue("eulerA_x",eulerA_x,28.378834901250);
  epsValue("gchi1_x",gchi1_x,1.743578734120);
  epsValue("gchi2_x",gchi2_x,1.379542040408);
  epsValue("gchi3_x",gchi3_x,1.411719976977);
  epsValue("gchi4_x",gchi4_x,1.896362778368);
  epsValue("gchi5_x",gchi5_x,1.360067563951);
  epsValue("gchi6_x",gchi6_x,1.392833927268);
  epsValue("halfbump_x1",Lib::halfbump_x1,0.004998940483);
  epsValue("halfbump_x4",halfbump_x4,-0.047139389935);
  epsValue("eta2_135",eta2_135,1.722494065481);
  epsValue("eta2_456",eta2_456,1.500247076264);
  epsValue("vol3_x_sqrt",vol3_x_sqrt,0.370600113929);
  epsValue("vol3f_x_lfun",vol3f_x_lfun,0.340976478480);
  epsValue("vol3f_x_sqrt2_lmplus",vol3f_x_sqrt2_lmplus,0.340747665892);
  epsValue("asn797k",asn797k,2.147917634601);
  epsValue("acs_sqrt_x1_d4",acs_sqrt_x1_d4,0.888630017028);
  epsValue("acs_sqrt_x2_d4",acs_sqrt_x2_d4,1.032880179256);
  epsValue("arclength_x_123",arclength_x_123,0.920267456658);
  epsValue("arclength_x_234",arclength_x_234,1.067419406823);
  epsValue("arclength_x_126",arclength_x_126,0.956254020546);
  epsValue("sol_euler_x_div_sqrtdelta",sol_euler_x_div_sqrtdelta,0.034565067428);
  epsValue("sol_euler246_x_div_sqrtdelta",sol_euler246_x_div_sqrtdelta,0.046001549036);
  epsValue("sol_euler345_x_div_sqrtdelta",sol_euler345_x_div_sqrtdelta,0.045968639642);
  epsValue("sol_euler156_x_div_sqrtdelta",sol_euler156_x_div_sqrtdelta,0.031150193819);
  epsValue("dih_x_div_sqrtdelta_posbranch",dih_x_div_sqrtdelta_posbranch,0.097899597826);
  epsValue("dih3_x_div_sqrtdelta_posbranch",dih3_x_div_sqrtdelta_posbranch,0.082852493168);
  epsValue("dih4_x_div_sqrtdelta_posbranch",dih4_x_div_sqrtdelta_posbranch,0.111027061541);
  epsValue("dih5_x_div_sqrtdelta_posbranch",dih5_x_div_sqrtdelta_posbranch,0.079438796838);
  epsValue("dih_x_126_s2",dih_x_126_s2,0.965572281503);
  epsValue("dih2_x_126_s2",dih2_x_126_s2,0.570741653951);
  epsValue("dih3_x_126_s2",dih3_x_126_s2,1.795272880367);
  epsValue("dih4_x_126_s2",dih4_x_126_s2,2.220680655245);
  epsValue("dih5_x_126_s2",dih5_x_126_s2,1.745179366760);
  epsValue("dih6_x_126_s2",dih6_x_126_s2,0.607909368960);
  epsValue("dih_x_135_s2",dih_x_135_s2,0.966153404013);
  epsValue("dih2_x_135_s2",dih2_x_135_s2,1.782590891418);
  epsValue("dih3_x_135_s2",dih3_x_135_s2,0.579646740440);
  epsValue("dih4_x_135_s2",dih4_x_135_s2,2.221591810849);
  epsValue("dih5_x_135_s2",dih5_x_135_s2,0.598205382204);
  epsValue("dih6_x_135_s2",dih6_x_135_s2,1.757569345670);
  epsValue("ldih_x_126_s2",ldih_x_126_s2,-0.003535559119);
  epsValue("ldih2_x_126_s2",ldih2_x_126_s2,0.516532004487);
  epsValue("ldih6_x_126_s2",ldih6_x_126_s2,0.438675515118);
  epsValue("ldih_x_135_s2",ldih_x_135_s2,-0.003537686969);
  epsValue("ldih3_x_135_s2",ldih3_x_135_s2,0.497555234675);
  epsValue("ldih5_x_135_s2",ldih5_x_135_s2,0.458639069727);
  epsValue("edge_flat2_x",Lib::edge_flat2_x,11.225847074301);
  epsValue("euler_3flat_x",euler_3flat_x,-0.056143552073);
  epsValue("euler_2flat_x",euler_2flat_x,9.635043711770);
  epsValue("euler_1flat_x",euler_1flat_x,19.090818302043);
  epsValue("rhazim_x",rhazim_x,1.591068282646);
  epsValue("rhazim2_x",rhazim2_x,1.140225421881);
  epsValue("rhazim3_x",rhazim3_x,1.173335485066);
  epsValue("taum_x",taum_x,0.211750937571);
  epsValue("taum_3flat_x",taum_3flat_x,1.801783790380);
  epsValue("taum_2flat_x",taum_2flat_x,0.382442539070);
  epsValue("taum_1flat_x",taum_1flat_x,-0.321592956561);
  epsValue("delta_x_126_s2",delta_x_126_s2,19.777600000000);
  epsValue("delta_x_135_s2",delta_x_135_s2,19.826800000000);
  epsValue("delta_pent_x",delta_pent_x,143.578427904000);
  epsValue("vol3_x_135_s2",vol3_x_135_s2,0.371060791665);
  epsValue("ldih_x_div_sqrtdelta_posbranch",ldih_x_div_sqrtdelta_posbranch,-0.000358471160);
  epsValue("ldih2_x_div_sqrtdelta_posbranch",ldih2_x_div_sqrtdelta_posbranch,0.073453769858);
  epsValue("ldih3_x_div_sqrtdelta_posbranch",ldih3_x_div_sqrtdelta_posbranch,0.071118646592);
  epsValue("ldih5_x_div_sqrtdelta_posbranch",ldih5_x_div_sqrtdelta_posbranch,0.060905061983);
  epsValue("ldih6_x_div_sqrtdelta_posbranch",ldih6_x_div_sqrtdelta_posbranch,0.058567229738);
  epsValue("ldih_x_n",ldih_x_n,-0.004953471695);
  epsValue("ldih_x_126_n",ldih_x_126_n,-0.003535559119);
  epsValue("ldih2_x_126_n",ldih2_x_126_n,0.516532004487);
  epsValue("ldih6_x_126_n",ldih6_x_126_n,0.438675515118);
  epsValue("ldih_x_135_n",ldih_x_135_n,-0.003537686969);
  epsValue("ldih3_x_135_n",ldih3_x_135_n,0.497555234675);
  epsValue("ldih5_x_135_n",ldih5_x_135_n,0.458639069727);
  epsValue("rhazim_x_div_sqrtdelta_posbranch",rhazim_x_div_sqrtdelta_posbranch,0.115141889980);
  epsValue("rhazim2_x_div_sqrtdelta_posbranch",rhazim2_x_div_sqrtdelta_posbranch,0.082515446704);
  epsValue("rhazim3_x_div_sqrtdelta_posbranch",rhazim3_x_div_sqrtdelta_posbranch,0.084911544529);
  epsValue("tau_residual_x",tau_residual_x,0.282568881213);
  epsValue("num1",Lib::num1,782.105600000000);
  epsValue("dnum1",dnum1,16.472000000000);
  //epsValue("num2",Lib::num2,13750.458367999760);
  //epsValue("num_combo1",Lib::num_combo1,611551.664967679884);
  //  epsValue("delta_y_LC",Lib::delta_y_LC,13736.192810182391);
  epsValue("delta_x1",delta_x1,2.122000000000);
  epsValue("mu6_x",mu6_x,0.021036374134);
  epsValue("taud_x",taud_x,0.292706094423);
  epsValue("taud_D2_num_x",taud_D2_num_x,-584.763202047616);
  epsValue("taud_D1_num_x",taud_D1_num_x,1.396045789581);
  epsValue("ups_126",Lib::ups_126,71.326400000000);
  epsValue("ups_126",Lib::ups_126,71.326400000000);
  epsValue("delta_126_x",delta_126_x(interval("0.140000"),interval("0.240000"),interval("0.340000")),-105.771664000000);
  epsValue("delta_234_x",delta_234_x(interval("0.140000"),interval("0.240000"),interval("0.340000")),-66.247800000000);
  epsValue("delta_135_x",delta_135_x(interval("0.140000"),interval("0.240000"),interval("0.340000")),-105.982464000000);
  epsValue("delta_sub1_x",delta_sub1_x(interval("0.140000")),7.518360000000);
  epsValue("taum_sub1_x",taum_sub1_x(interval("0.140000")),0.122046676350);
  epsValue("gamma3f_x_div_sqrtdelta",gamma3f_x_div_sqrtdelta(interval("0.140000"),interval("0.240000"),interval("0.340000")),-0.011756773994);
  epsValue("vol3f_456",vol3f_456(interval("0.140000")),0.464530693116);
  epsValue("gamma3_x",gamma3_x(interval("0.140000")),-0.005516047986);
  epsValue("gamma23_full8_x",gamma23_full8_x(interval("0.140000")),0.055415723962);
  epsValue("gamma23_keep135_x",gamma23_keep135_x(interval("0.140000")),0.033319887940);
  epsValue("mudLs_234_x",mudLs_234_x(interval("0.140000"),interval("0.240000"),interval("0.340000"),interval("0.440000"),interval("0.540000")),-31.277036910818);
  epsValue("mudLs_126_x",mudLs_126_x(interval("0.140000"),interval("0.240000"),interval("0.340000"),interval("0.440000"),interval("0.540000")),-48.325135995037);
  epsValue("mudLs_135_x",mudLs_135_x(interval("0.140000"),interval("0.240000"),interval("0.340000"),interval("0.440000"),interval("0.540000")),-48.349169797523); 
       cout << " -- done loading test_auto test" << endl << flush; }


 const char ver[] = "ver(3385:3386M,170M)";
 const char ineq_id[] = "7550003505 0 1 3";

 int testRun() // autogenerated code
	{
	interval tx[6]={interval("4."),interval("4."),interval("4."),(interval("3.01") * interval("3.01")),(interval("3.01") * interval("3.01")),(interval("3.01") * interval("3.01"))};
	interval tz[6]={interval("6.3504"),interval("6.3504"),interval("6.3504"),(interval("3.915") * interval("3.915")),(interval("3.915") * interval("3.915")),(interval("3.915") * interval("3.915"))};
	domain x = domain::lowerD(tx);
	domain z = domain::upperD(tz);
        domain x0=x;
        domain z0=z;
               Function F1 = (((Lib::unit ) * interval("0.712")) + (((rhazim_x ) * (-interval("1"))) + (((rhazim2_x ) * (-interval("1"))) + (((rhazim3_x ) * (-interval("1"))) + (((Lib::unit ) * (pi)) + (((Lib::unit ) * ((const1) * (pi))) + (((flat_term2_234_x ((interval("0")),(interval("4")),(interval("4")))) * (-interval("1"))) + (((mudLs_135_x ((interval("4")),(interval("10")),(interval("2.")),(interval("2.")),(interval("2.")))) * (-interval("1"))) + ((Lib::unit ) * ((pi) * (const1)))))))))));
       Function F2 = (eulerA_x );
       Function F3 = (delta_234_x ((interval("4")),(interval("4")),(interval("4"))));
       Function F4 = ((delta_234_x ((interval("6.3504")),(interval("4")),(interval("4")))) * (-interval("1")));
       Function F5 = ((delta_135_x ((interval("4")),(interval("4")),(interval("4")))) + ((Lib::unit ) * (-interval("16"))));
       Function F6 = (((Lib::unit ) * interval("100.")) + ((delta_135_x ((interval("4")),(interval("4")),(interval("4")))) * (-interval("1"))));
        const Function* I[6] = {&F1,&F2,&F3,&F4,&F5,&F6}; // len ...
        cellOption opt;
        opt.allowSharp = 0; // sharp
        opt.onlyCheckDeriv1Negative = 0; // checkderiv
         // other options.
	return  prove::recursiveVerifier(0,x,z,x0,z0,I,6,opt); // len
	}

main()
	{
	cout << "welcome " << endl << flush;
	moduleTest();
	selfTest();
	Timer tm;
	tm.start();
	time_t starttime = time(0);
	cout.precision(20);
	if (testRun()) {
	        time_t elapsed = time(0) - starttime;
		tm.stop();
		int cellcount = prove::get_cellcount();
		ofstream log;
 		char filename[]= //"/tmp/qed_log.txt";
		"/Users/thomashales/Desktop/googlecode/flyspeck/interval_code/qed_log_2012.txt";
		cout << "QED, ineq(" << ineq_id << "),";
		cout << " secs(" << elapsed << "), ";
		cout << " cells(" << cellcount << "), ";
		cout << ver << ", " << flush; 
		system ("date");
	        if (error::get_error_count() == 0) {
		  log.open (filename, ios::out | ios::app);
		log << "QED, ineq(" << ineq_id << "),";
		log << " secs(" << elapsed << "), ";
		log << " msecs(" << tm.duration() << "), ";
		log << " cells(" << cellcount << "), ";
		log << ver << ", " << flush; 
		log.close();
		char dater[300];	
		sprintf(dater,"date >> %s",filename);
		system (dater);
		}
		}
	else cout << "FAIL" ;
	cout << endl << flush;
	}
