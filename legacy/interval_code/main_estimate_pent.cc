/*
Code to compute dih_max, delta_y (min & max), taum (min)
on a given rectangle.

Project aborted. May 11, 2013 because of bad results,
but keep the code as an example of how to link
ocaml with C/C++ through printed output.

The ocaml link code appears at the bottom of the file.

 */


#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"
#include <assert.h>

// top section copied from t.cc.

class trialdata { public: trialdata(Minimizer M,char* s)
{ M.coutReport(s); };};

int trialcount = 50;

double sol0(

) { 
return ( ((3. * (acos((1. / 3.)))) - (pi())) ); 
}


double tau0(

) { 
return ( ((4. * (pi())) - (20. * (sol0()))) ); 
}


double hplus(

) { 
return ( 1.3254 ); 
}


double mm1(

) { 
return ( ((sol0()) * ((sqrt(8.)) / (tau0()))) ); 
}


double mm2(

) { 
return ( (((6. * (sol0())) - (pi())) * ((sqrt(2.)) / (6. * (tau0())))) ); 
}


double vol_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((sqrt((delta_x(x1,x2,x3,x4,x5,x6)))) / 12.) ); 
}


double sqrt8(

) { 
return ( (sqrt(8.)) ); 
}


double sqrt2(

) { 
return ( (sqrt(2.)) ); 
}


double sqrt3(

) { 
return ( (sqrt(3.)) ); 
}


double rho_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((((-x1) * (x1 * (x4 * x4))) - (x2 * (x2 * (x5 * x5)))) - (x3 * (x3 * (x6 * x6)))) + ((2. * (x1 * (x2 * (x4 * x5)))) + ((2. * (x1 * (x3 * (x4 * x6)))) + (2. * (x2 * (x3 * (x5 * x6))))))) ); 
}


double rad2_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((rho_x(x1,x2,x3,x4,x5,x6)) / ((delta_x(x1,x2,x3,x4,x5,x6)) * 4.)) ); 
}


double ups_x(
double x1,double x2,double x6
) { 
return ( (((((-x1) * x1) - (x2 * x2)) - (x6 * x6)) + ((2. * (x1 * x6)) + ((2. * (x1 * x2)) + (2. * (x2 * x6))))) ); 
}


double eta_x(
double x1,double x2,double x3
) { 
return ( (sqrt(((x1 * (x2 * x3)) / (ups_x(x1,x2,x3))))) ); 
}


double eta_y(
double y1,double y2,double y3
) { 
return ( (eta_x((y1 * y1),(y2 * y2),(y3 * y3))) ); 
}


double volR(
double a,double b,double c
) { 
return ( ((sqrt((a * (a * (((b * b) - (a * a)) * ((c * c) - (b * b))))))) / 6.) ); 
}


double norm2hh(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( ((real_pow(((y1 - (hminus())) - (hplus())),2.)) + ((real_pow((y2 - 2.),2.)) + ((real_pow((y3 - 2.),2.)) + ((real_pow((y4 - 2.),2.)) + ((real_pow((y5 - 2.),2.)) + (real_pow((y6 - 2.),2.))))))) ); 
}


double arclength(
double a,double b,double c
) { 
return ( (((pi()) / 2.) + (atn2( (sqrt((ups_x((a * a),(b * b),(c * c))))),(((c * c) - (a * a)) - (b * b))))) ); 
}


double regular_spherical_polygon_area(
double ca,double k
) { 
return ( ((2. * (pi())) - (2. * (k * (asn((ca * (sin(((pi()) / k))))))))) ); 
}


double beta_bump_force_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( ((bump((y1 / 2.))) - (bump((y4 / 2.)))) ); 
}


double a_spine5(

) { 
return ( 0.0560305 ); 
}


double b_spine5(

) { 
return ( (-0.0445813) ); 
}


double beta_bump_lb(

) { 
return ( (-0.005) ); 
}


double marchal_quartic(
double h
) { 
return ( (((sqrt(2.)) - h) * ((h - (hplus())) * ((((9. * (real_pow(h,2.))) - (17. * h)) + 3.) / (((sqrt(2.)) - 1.) * (5. * ((hplus()) - 1.)))))) ); 
}


double vol2r(
double y,double r
) { 
return ( (2. * ((pi()) * (((r * r) - (real_pow((y / 2.),2.))) / 3.))) ); 
}


double tame_table_d(
double r,double s
) { 
return ( (((r + (2. * s)) > 3.) ? ((0.103 * (2. - s)) + (0.2759 * (r + ((2. * s) - 4.)))) : 0.) ); 
}


double delta_x4(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((((-x2) * x3) - (x1 * x4)) + ((x2 * x5) + (((x3 * x6) - (x5 * x6)) + (x1 * ((-x1) + (x2 + ((x3 - x4) + (x5 + x6)))))))) ); 
}


double dih_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((pi()) / 2.) + (atn2( (sqrt((4. * (x1 * (delta_x(x1,x2,x3,x4,x5,x6)))))),(-(delta_x4(x1,x2,x3,x4,x5,x6)))))) ); 
}


double sol_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((dih_x(x1,x2,x3,x4,x5,x6)) + ((dih_x(x2,x3,x1,x5,x6,x4)) + ((dih_x(x3,x1,x2,x6,x4,x5)) - (pi())))) ); 
}


double delta4_squared_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (real_pow((delta_x4(x1,x2,x3,x4,x5,x6)),2.)) ); 
}


double x1_delta_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (x1 * (delta_x(x1,x2,x3,x4,x5,x6))) ); 
}


double quadratic_root_plus_curry(
double a,double b,double c
) { 
return ( (((-b) + (sqrt(((real_pow(b,2.)) - (4. * (a * c)))))) / (2. * a)) ); 
}


double edge_flat(
double y1,double y2,double y3,double y5,double y6
) { 
return ( (sqrt((quadratic_root_plus_curry((y1 * y1),(((y1 * y1) * (y1 * y1)) + ((((y3 * y3) - (y5 * y5)) * ((y2 * y2) - (y6 * y6))) - ((y1 * y1) * ((y2 * y2) + ((y3 * y3) + ((y5 * y5) + (y6 * y6))))))),(((y1 * y1) * ((y3 * y3) * (y5 * y5))) + ((((y1 * y1) * ((y2 * y2) * (y6 * y6))) - ((y3 * y3) * (((y1 * y1) + (((y2 * y2) - (y3 * y3)) + ((y5 * y5) - (y6 * y6)))) * (y6 * y6)))) - ((y2 * y2) * ((y5 * y5) * (((y1 * y1) - (y2 * y2)) + (((y3 * y3) - (y5 * y5)) + (y6 * y6))))))))))) ); 
}


double const1(

) { 
return ( ((sol_y(2.,2.,2.,2.,2.,2.)) / (pi())) ); 
}


double taum(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (((sol_y(y1,y2,y3,y4,y5,y6)) * (1. + (const1()))) - ((const1()) * ((lnazim(y1,y2,y3,y4,y5,y6)) + ((lnazim(y2,y3,y1,y5,y6,y4)) + (lnazim(y3,y1,y2,y6,y4,y5)))))) ); 
}

void c0(int numargs,int whichFn,double* y_mangle__, double* ret,void*) {
double y1 = y_mangle__[0];
double y2 = y_mangle__[1];
double y3 = y_mangle__[2];
double y4 = y_mangle__[3];
double y5 = y_mangle__[4];
double y6 = y_mangle__[5];
 *ret =  ((0.0001 - (delta_y(y1,y2,y3,y4,y5,y6))));
}

void t1(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double y1 = y_mangle__[0];
double y2 = y_mangle__[1];
double y3 = y_mangle__[2];
double y4 = y_mangle__[3];
double y5 = y_mangle__[4];
double y6 = y_mangle__[5];
 *ret = taum(y1,y2,y3,y4,y5,y6);
}

void t2(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double y1 = y_mangle__[0];
double y2 = y_mangle__[1];
double y3 = y_mangle__[2];
double y4 = y_mangle__[3];
double y5 = y_mangle__[4];
double y6 = y_mangle__[5];
 *ret = - dih_y(y1,y2,y3,y4,y5,y6);
}

void t3(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double y1 = y_mangle__[0];
double y2 = y_mangle__[1];
double y3 = y_mangle__[2];
double y4 = y_mangle__[3];
double y5 = y_mangle__[4];
double y6 = y_mangle__[5];
 *ret = - delta_y(y1,y2,y3,y4,y5,y6);
}

void t4(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double y1 = y_mangle__[0];
double y2 = y_mangle__[1];
double y3 = y_mangle__[2];
double y4 = y_mangle__[3];
double y5 = y_mangle__[4];
double y6 = y_mangle__[5];
 *ret = delta_y(y1,y2,y3,y4,y5,y6);
}

Minimizer m0(double xmin[6],double xmax[6],int nc,int whicht) {
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.cFunc = c0;
	M.func = (whicht == 1 ? t1 :
		   (whicht == 2 ? t2 :
		    (whicht == 3 ? t3 : t4)));
	return M;
}

int main (int argc, char *argv[]) {
  if (!(argc == 14))  { cout << "argc=14 expected" << flush; exit( 0) ; };
  int whicht = atoi(argv[1]);
  int nc = ( whicht <2 ? 1 : 0);

  double x[6];
  double z[6];
  for (int i=0;i<6;i++) { x[i] = atof(argv[2+i]); }
  for (int i=0;i<6;i++) { z[i] = atof(argv[8+i]); }


  trialdata d0(m0(x,z,nc,whicht),"main_estimate_pent");


}

/*
let sprintf = Printf.sprintf;;

let phi2 = 3.23607;;

let float3 i = List.nth [(2.0,2.1);(2.1,2.3);(2.3,2.52)] i;;
let float3a i = List.nth [(3.01,3.08);(3.08,3.16);(3.16,phi2)   ] i;;
let float4 i = List.nth [(2.0,2.1);(2.1,2.25);(2.25,2.40);(2.40,2.52)] i;;
let float5 i = List.nth [(2.0,2.07);(2.07,2.17);(2.17,2.30);(2.30,2.41);(2.41,2.52)] i;;

let ear_range i1 i2 i3 i6 = 
  unzip [float3 i1; float4 i2; float5 i3; (2.0,2.0); (2.0,2.0); float3a i6];;

let a_range i1 i2 i3 i5 i6 = 
  unzip [float3 i1;float4 i2;float4 i3; (2.0,2.0); float3a i5;float3a i6];;

let cfsqp_string (f, r) = 
  let ([x1;x2;x3;x4;x5;x6],[z1;z2;z3;z4;z5;z6]) = r in
  let com = sprintf "~/Desktop/googlecode/flyspeck/cfsqp/main_estimate_pent.o %d %f %f %f %f %f %f %f %f %f %f %f %f | tee /tmp/pent.txt | grep 'constrained' | sed 's/constrained min: //'" f x1 x2 x3 x4 x5 x6 z1 z2 z3 z4 z5 z6 in
  let (ic,oc) = Unix.open_process(com) in 
  let inp = Flyspeck_lib.load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
    inp;;

let cfsqp_value (f,r) = 
  float_of_string (hd (cfsqp_string(f,r)));;

let delta_min r = cfsqp_value (4,r);;
let delta_max r =  -. cfsqp_value (3,r);;
let taum_min r = cfsqp_value (1,r);;
let dih_max r = -. cfsqp_value (2,r);;

taum_min (ear_range 0 1 4 2);;
taum_min (a_range 0 0 1 2 2);;

dih_max([2.;2.;2.;2.;3.01;3.01],[2.52;2.52;2.52;2.;3.24;3.24]);;
taum_min([2.;2.;2.;2.;3.01;3.01],[2.52;2.52;2.52;2.;3.24;3.24]);;
*/
