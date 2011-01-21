// The top part of the code is machine generated.
// The end is hand crafted.

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"
#include "2065952723A.h"

class trialdata { public: trialdata(Minimizer M,char* s) { M.coutReport(s); };};
int trialcount = 200;

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
return ( ( ((r + (2. * s)) > 3.) ? ((0.103 * (2. - s)) + (0.2759 * (r + ((2. * s) - 4.)))) : 0.) ); 
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


double flat_term(
double y
) { 
return ( ((sol0()) * ((y - (2. * (h0()))) / ((2. * (h0())) - 2.))) ); 
}


double taum_y1(
double a,double b,double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (taum(2.,2.,2.,a,b,y1)) ); 
}


double taum_y2(
double a,double b,double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (taum(2.,2.,2.,a,b,y2)) ); 
}


double taum_y1_y2(
double a,double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (taum(2.,2.,2.,a,y1,y2)) ); 
}


double arclength_y1(
double a,double b,double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (arclength(y1,a,b)) ); 
}


double arclength_y2(
double a,double b,double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (arclength(y2,a,b)) ); 
}


double arc_hhn(

) { 
return ( (arclength((2. * (h0())),(2. * (h0())),2.)) ); 
}


double asn797k(
double k,double x2,double x3,double x4,double x5,double x6
) { 
return ( (k * (asn(((cos(0.797)) * (sin(((pi()) / k))))))) ); 
}


double asnFnhk(
double h,double k,double x3,double x4,double x5,double x6
) { 
return ( (k * (asn((((h * ((sqrt3()) / 4.)) + ((sqrt((1. - (real_pow((h / 2.),2.))))) / 2.)) * (sin(((pi()) / k))))))) ); 
}


double lfun_y1(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (lfun(y1)) ); 
}


double arclength_x_123(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (arclength((sqrt(x1)),(sqrt(x2)),(sqrt(x3)))) ); 
}


double arclength_x_345(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (arclength((sqrt(x3)),(sqrt(x4)),(sqrt(x5)))) ); 
}


double acs_sqrt_x1_d4(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (acos(((sqrt(x1)) / 4.))) ); 
}


double acs_sqrt_x2_d4(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (acos(((sqrt(x2)) / 4.))) ); 
}


double tauq(
double y1,double y2,double y3,double y4,double y5,double y6,double y7,double y8,double y9
) { 
return ( ((taum(y1,y2,y3,y4,y5,y6)) + (taum(y7,y2,y3,y4,y8,y9))) ); 
}


double enclosed(
double y1,double y2,double y3,double y4,double y5,double y6,double y7,double y8,double y9
) { 
return ( (sqrt((quadratic_root_plus_curry((((-1.) * (real_pow((y6 * y6),2.))) + (((-1.) * (real_pow(((y5 * y5) + ((-1.) * (y4 * y4))),2.))) + (2. * ((y6 * y6) * ((y5 * y5) + (y4 * y4)))))),(2. * (((real_pow((y5 * y5),2.)) * ((y2 * y2) + (y8 * y8))) + (((real_pow((y6 * y6),2.)) * ((y3 * y3) + (y9 * y9))) + (((y4 * y4) * (((y7 * y7) * ((y4 * y4) + (((-1.) * (y2 * y2)) + ((-1.) * (y3 * y3))))) + (((y8 * y8) * (y3 * y3)) + (((y1 * y1) * ((2. * (y7 * y7)) + ((y4 * y4) + (((-1.) * (y8 * y8)) + ((-1.) * (y9 * y9)))))) + ((y2 * y2) * (y9 * y9)))))) + (((-1.) * ((y5 * y5) * (((y4 * y4) * (y2 * y2)) + (((y4 * y4) * (y8 * y8)) + (((-2.) * ((y2 * y2) * (y8 * y8))) + (((y7 * y7) * ((y4 * y4) + ((y2 * y2) + ((-1.) * (y3 * y3))))) + (((y8 * y8) * (y3 * y3)) + (((y1 * y1) * ((y4 * y4) + ((y8 * y8) + ((-1.) * (y9 * y9))))) + ((y2 * y2) * (y9 * y9)))))))))) + ((y6 * y6) * ((2. * ((y5 * y5) * (y4 * y4))) + (((-1.) * ((y1 * y1) * (y4 * y4))) + (((-1.) * ((y7 * y7) * (y4 * y4))) + (((-1.) * ((y5 * y5) * (y2 * y2))) + (((y7 * y7) * (y2 * y2)) + (((-1.) * ((y5 * y5) * (y8 * y8))) + (((y1 * y1) * (y8 * y8)) + (((-1.) * ((y5 * y5) * (y3 * y3))) + (((-1.) * ((y7 * y7) * (y3 * y3))) + (((-1.) * ((y4 * y4) * (y3 * y3))) + (((-1.) * ((y8 * y8) * (y3 * y3))) + (((-1.) * ((y5 * y5) * (y9 * y9))) + (((-1.) * ((y1 * y1) * (y9 * y9))) + (((-1.) * ((y4 * y4) * (y9 * y9))) + (((-1.) * ((y2 * y2) * (y9 * y9))) + (2. * ((y3 * y3) * (y9 * y9)))))))))))))))))))))))),(((-1.) * ((real_pow((y7 * y7),2.)) * ((real_pow((y4 * y4),2.)) + ((real_pow(((y2 * y2) + ((-1.) * (y3 * y3))),2.)) + ((-2.) * ((y4 * y4) * ((y2 * y2) + (y3 * y3)))))))) + (((-1.) * (real_pow((((y5 * y5) * (y2 * y2)) + (((-1.) * ((y5 * y5) * (y8 * y8))) + (((-1.) * ((y6 * y6) * (y3 * y3))) + (((y8 * y8) * (y3 * y3)) + (((y6 * y6) * (y9 * y9)) + ((-1.) * ((y2 * y2) * (y9 * y9)))))))),2.))) + (((-1.) * ((real_pow((y1 * y1),2.)) * ((real_pow((y4 * y4),2.)) + ((real_pow(((y8 * y8) + ((-1.) * (y9 * y9))),2.)) + ((-2.) * ((y4 * y4) * ((y8 * y8) + (y9 * y9)))))))) + (((-2.) * ((y7 * y7) * (((-2.) * ((y4 * y4) * ((y2 * y2) * (y3 * y3)))) + (((y4 * y4) * ((y8 * y8) * (y3 * y3))) + (((y2 * y2) * ((y8 * y8) * (y3 * y3))) + (((-1.) * ((y8 * y8) * (real_pow((y3 * y3),2.)))) + (((y5 * y5) * (((-1.) * (real_pow((y2 * y2),2.))) + (((y4 * y4) * ((y2 * y2) + ((-1.) * (y8 * y8)))) + (((y8 * y8) * (y3 * y3)) + ((y2 * y2) * ((y8 * y8) + ((y3 * y3) + ((-2.) * (y9 * y9))))))))) + (((y4 * y4) * ((y2 * y2) * (y9 * y9))) + (((-1.) * ((real_pow((y2 * y2),2.)) * (y9 * y9))) + (((y2 * y2) * ((y3 * y3) * (y9 * y9))) + ((y6 * y6) * (((y4 * y4) * ((y3 * y3) + ((-1.) * (y9 * y9)))) + (((y3 * y3) * (((-2.) * (y8 * y8)) + (((-1.) * (y3 * y3)) + (y9 * y9)))) + ((y2 * y2) * ((y3 * y3) + (y9 * y9)))))))))))))))) + (2. * ((y1 * y1) * (((y6 * y6) * ((y4 * y4) * (y3 * y3))) + (((-1.) * ((y6 * y6) * ((y8 * y8) * (y3 * y3)))) + (((-1.) * ((y4 * y4) * ((y8 * y8) * (y3 * y3)))) + (((real_pow((y8 * y8),2.)) * (y3 * y3)) + (((-1.) * ((y6 * y6) * ((y4 * y4) * (y9 * y9)))) + ((2. * ((y6 * y6) * ((y2 * y2) * (y9 * y9)))) + (((-1.) * ((y4 * y4) * ((y2 * y2) * (y9 * y9)))) + (((-1.) * ((y6 * y6) * ((y8 * y8) * (y9 * y9)))) + ((2. * ((y4 * y4) * ((y8 * y8) * (y9 * y9)))) + (((-1.) * ((y2 * y2) * ((y8 * y8) * (y9 * y9)))) + (((-1.) * ((y6 * y6) * ((y3 * y3) * (y9 * y9)))) + (((-1.) * ((y8 * y8) * ((y3 * y3) * (y9 * y9)))) + (((y6 * y6) * (real_pow((y9 * y9),2.))) + (((y2 * y2) * (real_pow((y9 * y9),2.))) + (((y5 * y5) * (((y4 * y4) * ((y2 * y2) + ((-1.) * (y8 * y8)))) + (((y8 * y8) * ((y8 * y8) + ((2. * (y3 * y3)) + ((-1.) * (y9 * y9))))) + ((-1.) * ((y2 * y2) * ((y8 * y8) + (y9 * y9))))))) + ((y7 * y7) * ((real_pow((y4 * y4),2.)) + ((((y2 * y2) + ((-1.) * (y3 * y3))) * ((y8 * y8) + ((-1.) * (y9 * y9)))) + ((-1.) * ((y4 * y4) * ((y2 * y2) + ((y8 * y8) + ((y3 * y3) + (y9 * y9)))))))))))))))))))))))))))))))))) ); 
}


double sol_euler_x_div_sqrtdelta(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((matan(((delta_x(x1,x2,x3,x4,x5,x6)) / (4. * (real_pow(((sqrt((x1 * (x2 * x3)))) + (((sqrt(x1)) * ((x2 + (x3 - x4)) / 2.)) + (((sqrt(x2)) * ((x1 + (x3 - x5)) / 2.)) + ((sqrt(x3)) * ((x1 + (x2 - x6)) / 2.))))),2.)))))) / ((sqrt((x1 * (x2 * x3)))) + (((sqrt(x1)) * ((x2 + (x3 - x4)) / 2.)) + (((sqrt(x2)) * ((x1 + (x3 - x5)) / 2.)) + ((sqrt(x3)) * ((x1 + (x2 - x6)) / 2.)))))) ); 
}


double dih_x_div_sqrtdelta_posbranch(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((sqrt((4. * x1))) / (delta_x4(x1,x2,x3,x4,x5,x6))) * (matan(((4. * (x1 * (delta_x(x1,x2,x3,x4,x5,x6)))) / (real_pow((delta_x4(x1,x2,x3,x4,x5,x6)),2.)))))) ); 
}


double surfR(
double a,double b,double c
) { 
return ( (3. * ((volR(a,b,c)) / a)) ); 
}


double surfRy(
double y1,double y2,double y6,double c
) { 
return ( (surfR((y1 / 2.),(eta_y(y1,y2,y6)),c)) ); 
}


double surfRdyc2(
double y1,double y2,double y6,double c2
) { 
return ( ((surfRy(y1,y2,y6,(sqrt(c2)))) + (surfRy(y2,y1,y6,(sqrt(c2))))) ); 
}


double surfy(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( ((surfRy(y1,y2,y6,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6))))))) + ((surfRy(y2,y1,y6,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6))))))) + ((surfRy(y2,y3,y4,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6))))))) + ((surfRy(y3,y2,y4,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6))))))) + ((surfRy(y3,y1,y5,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6))))))) + (surfRy(y1,y3,y5,(sqrt((rad2_x((y1 * y1),(y2 * y2),(y3 * y3),(y4 * y4),(y5 * y5),(y6 * y6)))))))))))) ); 
}


double dih4_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y4,y2,y6,y1,y5,y3)) ); 
}


double dih5_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y5,y1,y6,y2,y4,y3)) ); 
}


double dih6_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y6,y1,y5,y3,y4,y2)) ); 
}


double num1(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( ((-4.) * (((real_pow(a2,2.)) * e1) + ((8. * ((b2 - c2) * (e2 - e3))) - (a2 * ((16. * e1) + (((b2 - 8.) * e2) + ((c2 - 8.) * e3))))))) ); 
}

double num1m(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
  return -num1(e1,e2,e3,a2,b2,c2);
}


double num2(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( (8. * ((2. * ((real_pow(a2,5.)) * e1)) + (((-256.) * ((real_pow((b2 + ((-1.) * c2)),3.)) * (e2 + ((-1.) * e3)))) + (((-1.) * ((real_pow(a2,3.)) * ((2. * (((-256.) + ((real_pow(b2,2.)) + (((-2.) * (b2 * c2)) + (real_pow(c2,2.))))) * e1)) + (((((real_pow(b2,2.)) * ((-8.) + c2)) + (((-16.) * (b2 * (3. + c2))) + (16. * (16. + (9. * c2))))) * e2) + (((b2 * (144. + (((-16.) * c2) + (real_pow(c2,2.))))) + ((-8.) * ((-32.) + ((6. * c2) + (real_pow(c2,2.)))))) * e3))))) + (((real_pow(a2,4.)) * (((-64.) * e1) + ((-6.) * ((((-8.) + b2) * e2) + (((-8.) + c2) * e3))))) + (((-2.) * ((real_pow(a2,2.)) * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * e2) + ((8. * (c2 * ((4. * e1) + ((9. * e2) + ((-7.) * e3))))) + ((384. * (e2 + ((-1.) * e3))) + (((-1.) * ((real_pow(c2,2.)) * e3)) + (b2 * (((-32.) * e1) + (((56. + ((-9.) * c2)) * e2) + (9. * (((-8.) + c2) * e3)))))))))))) + (16. * (a2 * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * (e2 + ((-3.) * e3))) + (((-4.) * (b2 * ((8. * e1) + ((((-20.) + (3. * c2)) * e2) + ((-3.) * (((-4.) + c2) * e3)))))) + (c2 * ((32. * e1) + ((3. * ((16. + c2) * e2)) + ((-1.) * ((80. + c2) * e3)))))))))))))))) ); 
}


double num_combo1(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( ((2. / 25.) * (((-2.) * ((real_pow(a2,5.)) * e1)) + ((256. * ((real_pow((b2 + ((-1.) * c2)),3.)) * (e2 + ((-1.) * e3)))) + (((real_pow(a2,3.)) * ((2. * (((-256.) + ((real_pow(b2,2.)) + (((-2.) * (b2 * c2)) + (real_pow(c2,2.))))) * e1)) + (((((real_pow(b2,2.)) * ((-8.) + c2)) + (((-16.) * (b2 * (3. + c2))) + (16. * (16. + (9. * c2))))) * e2) + (((b2 * (144. + (((-16.) * c2) + (real_pow(c2,2.))))) + ((-8.) * ((-32.) + ((6. * c2) + (real_pow(c2,2.)))))) * e3)))) + ((2. * ((real_pow(a2,4.)) * ((32. * e1) + (3. * ((((-8.) + b2) * e2) + (((-8.) + c2) * e3)))))) + ((200. * (real_pow((((real_pow(a2,2.)) * e1) + ((8. * ((b2 + ((-1.) * c2)) * (e2 + ((-1.) * e3)))) + ((-1.) * (a2 * ((16. * e1) + ((((-8.) + b2) * e2) + (((-8.) + c2) * e3))))))),2.))) + ((2. * ((real_pow(a2,2.)) * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * e2) + ((8. * (c2 * ((4. * e1) + ((9. * e2) + ((-7.) * e3))))) + ((384. * (e2 + ((-1.) * e3))) + (((-1.) * ((real_pow(c2,2.)) * e3)) + (b2 * (((-32.) * e1) + (((56. + ((-9.) * c2)) * e2) + (9. * (((-8.) + c2) * e3)))))))))))) + ((-16.) * (a2 * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * (e2 + ((-3.) * e3))) + (((-4.) * (b2 * ((8. * e1) + ((((-20.) + (3. * c2)) * e2) + ((-3.) * (((-4.) + c2) * e3)))))) + (c2 * ((32. * e1) + ((3. * ((16. + c2) * e2)) + ((-1.) * ((80. + c2) * e3))))))))))))))))) ); 
}



double num2m(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
  return - num2(e1,e2,e3,a2,b2,c2);
}


double flat_term_x(
double x
) { 
return ( (flat_term((sqrt(x)))) ); 
}


double upper_dih_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (2. * ((sqrt(x1)) * ((sqp((delta_x(x1,x2,x3,x4,x5,x6)))) * ((matan((4. * (x1 * ((delta_x(x1,x2,x3,x4,x5,x6)) / (real_pow((delta_x4(x1,x2,x3,x4,x5,x6)),2.))))))) / (delta_x4(x1,x2,x3,x4,x5,x6)))))) ); 
}


double eulerA_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((sqrt(x1)) * ((sqrt(x2)) * (sqrt(x3)))) + (((sqrt(x1)) * ((x2 + (x3 - x4)) / 2.)) + (((sqrt(x2)) * ((x1 + (x3 - x5)) / 2.)) + ((sqrt(x3)) * ((x1 + (x2 - x6)) / 2.))))) ); 
}


// Start hand-crafted code.

/* A simple simplex method for 2-d.
The data is a list of length 2*n,
d00 d01 d10 d11 d20 d21 ....
(0,dj0) and (1,dj1) are two points determining a line.
The problem is to form the lower hull of these lines between x=0 and x=1, and to compute the highest point on the hull.  The return
value (between 0 and 1) is the x coordinate of this highest point.

For example, if n=2, and the data is (1,4,3,2), the two lines
are those passing through
(0,1) (1,4) and
(0,3) (1,2) respectively.

The lines meet at (0.5,2.5), and the procedure returns 0.5.

But if the data is (1,4,2,3), the procedure returns 1.0.
 */

double simplex2Dalpha(const double* data, int n) {

  // convert data to pairs.
  double d[n][2];
  double slope[n];
  for (int i=0;i<n;i++) {
    d[i][0] = data[2*i];
    d[i][1] = data[2*i+1];
    slope[i] = d[i][1]-d[i][0];
  }
 
  int p=0;  // pivot.
  double dmin = d[p][0];
  for (int i=0;i<n;i++) {
    if (d[i][0] < dmin || (d[i][0]==dmin && slope[i]< slope[p])) 
      { p = i; dmin = d[i][0]; }
  }
  double alpha = 0;
  
  // compute alpha, beta.   // alpha = beta/(1+beta).
  int counter = 500;
  while (counter--) {
    if (d[p][1] <= d[p][0]) return alpha; // peak has been reached.
    if (!counter) { 
      cout << "simplex resources expended" << flush; 
      exit(0); }
    double alphamin = 1.0;
    int q = -1; // new pivot
    for (int i=0;i<n;i++) {
      if (d[i][1] < d[p][1] && d[i][0] > d[p][0]) {
	double betatemp = (d[i][0]-d[p][0])/(d[p][1]-d[i][1]);
	double alphatemp = betatemp/ (1.0 + betatemp);
	if (alpha < alphatemp && 
	    (alphatemp < alphamin || 
	     (alphatemp==alphamin && (q>=0) && slope[i] < slope[q])))
	  { q=i; alphamin = alphatemp; }
      }
    }
    if (q < 0) {  // no new pivot found.
      assert(alphamin==1.0);
      return alphamin;  
    }
    assert(alphamin >= alpha); // alpha sequence should be increasing!
    // set new pivot and repeat
    p = q; alpha= alphamin;
  }
  
}



void c0(int numargs,int whichFn,double* y_mangle__, double* ret,void*) {
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
switch(whichFn) {
default: *ret = 0; break; }}


void t_num1m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num1m(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}


void t_num1(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num1(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}


void t_num2m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num2m(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}

void t_combo(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num_combo1(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}

double global_alpha=0 ; // sorry about the global variable!

void t_varcombo(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
 *ret = (1.0-fabs(global_alpha)) * num2m(e1,e2,e3,a2,b2,c2) +
              global_alpha*num1(e1,e2,e3,a2,b2,c2);
  }

double numsgn(double sgn, double y_mangle__[6],int parity) {
  double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
 if (0==parity) return num2m(e1,e2,e3,a2,b2,c2);
 if (sgn>0) return num1(e1,e2,e3,a2,b2,c2);
 return num1m(e1,e2,e3,a2,b2,c2);
}


Minimizer m_num1m(double xmin[6],double xmax[6]) {
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t_num1m;
	M.cFunc = c0;
	return M;
}

Minimizer m_num1(double xmin[6],double xmax[6]) {
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t_num1;
	M.cFunc = c0;
	return M;
}

Minimizer m_num2m(double xmin[6],double xmax[6]) {
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t_num2m;
	M.cFunc = c0;
	return M;
}


Minimizer m_combo(double xmin[6],double xmax[6]) {
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t_combo;
	M.cFunc = c0;
	return M;
};

Minimizer m_varcombo(double xmin[6],double xmax[6]) {
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t_varcombo;
	M.cFunc = c0;
	return M;
};


double rectangle_partial=0;
double rectangle_total=0;

double rectangle(double xmin[6],double xmax[6]) {
  double v = 1;
  for (int i=0;i<6;i++) { v *= (xmax[i] - xmin[i]); }
  return v;
}

double percent_done() {
  return rectangle_partial / rectangle_total;
}

void set_rectangle(double xmin[6],double xmax[6]) {
  rectangle_total = rectangle(xmin,xmax);
}

// split on the final three variables

int split3(const double xmin[6],const double xmax[6],
	   double rmin[2][6],double rmax[2][6]) {  
	int j_wide=0; /* init j_wide */ {
	double w = xmax[0]-xmin[0]; 
	for (int j=0;j<6;j++) {
	  if (xmax[j]-xmin[j] > w) { j_wide = j; w = xmax[j]-xmin[j]; }
	  }
	//cout << w << " " << j_wide << endl << flush;
	}
	double y = (xmin[j_wide]+xmax[j_wide])/2.0;
	for (int k=0;k<2;k++) 	{
	  for (int j=0;j<6;j++) { rmin[k][j] = xmin[j]; rmax[k][j]=xmax[j]; }
	  (k? rmin[k][j_wide] = y : rmax[k][j_wide] = y);
	}
	return j_wide;
}


int counter = 0;
int lastprintcount = 0;
int combcounter =0;
int printspan=40;

int getCounter() {
  return counter;
}


int setStrategy (double xmin[6],double xmax[6],strategy& s,int recurse)
{
  counter ++;
  double eps = 10.0; // was 0.01.

  Minimizer zer1 = m_num1(xmin,xmax);
  Minimizer zer1m = m_num1m(xmin,xmax);
  Minimizer zer2m = m_num2m(xmin,xmax);

  double m1 = zer1.optimize();
  double m1m = zer1m.optimize();
  double m2m = zer2m.optimize();
  double mm = max(m2m,max(m1,m1m));
  int which = (mm==m1 ? 1 : (mm==m1m ? 2 : 3));
  if (mm > eps) { 
    switch (which) {
    case 1 : s.mode = strategy::n1; break;
    case 2: s.mode = strategy::n1m; break;
    default : s.mode = strategy::n2m; break;
    }
    rectangle_partial += rectangle(xmin,xmax); 
    return 1; 
  }

  // check for a C/E.
  double mc = m_combo(xmin,xmax).optimize();
  if (mc < 0) {
    cout << "CE found: " << mc << flush << endl;
    for (int i=0;i<6;i++) cout << xmin[i] << " " << xmax[i] << endl;
    exit(0);
  }

  // look for a combination of num2 and num1 that works.
  // set sign of num1
  {
  double sign1 = (numsgn(1.0,zer2m.x,1) > 0.0 ? 1.0 : -1.0);
  // generate 64= 2^6 data points:
  double data[2 * 64];
  for (int i=0;i<2;i++)
    for (int j=0;j<64;j++) {
      int u=1;
      double x[6];
      for (int k=0;k<6;k++) { 
	int bit =  (j/u) % 2; u *= 2;  // kth bit of binary rep of j.
	x[k]= (bit ? xmax[k] : xmin[k] ); 
      }
      data[2 * j + i] = numsgn(sign1,x,i);
    }
  global_alpha = sign1 *simplex2Dalpha(data,64);
  }

  // check if it works
  Minimizer znn = m_varcombo(xmin,xmax);
  double nn = znn.optimize();
  if (nn > eps) { 
    s.mode = strategy::merge;
    s.alpha = global_alpha;
    combcounter++; 
    rectangle_partial += rectangle(xmin,xmax); 
    return 1; } 
  
  // print some statistics
  double w = 0;
  for (int i=0;i<5;i++) { w += xmax[i]-xmin[i]; }
  if (mm < 0 && (lastprintcount + printspan<= counter)) {
      cout.precision(3);
      lastprintcount = counter;
      cout << "w: " << which << " " << counter << " " <<  combcounter << " " << mm/w << " " << nn/w << " w:" << w << " a:" << global_alpha ;
      cout.precision(6);
      cout << " f:" << rectangle_partial/rectangle_total << endl << flush; } 

  // subdivide recursively:
  double rmin[2][6], rmax[2][6];
  s.mode = strategy::split;
  s.splitvar =split3(xmin,xmax,rmin,rmax);
  return (recurse ? (setStrategy(rmin[0],rmax[0],s,recurse) && 
		     (setStrategy(rmin[1],rmax[1],s,recurse))) : 0);;
}

int setStrategy206A (double xmin[6],double xmax[6],strategy& s) {
  return setStrategy(xmin,xmax,s,0);
}


int qmain ()  { // constant changed to 15.53 on Jan 21, 2011.

  double xmin[6]= {
1.,1.,1.,(real_pow((2. / (h0())),2.)),(real_pow((2. / (h0())),2.)),(real_pow((2. / (h0())),2.))
};
  double xmax[6]= {
(1. + ((sol0()) / (pi()))),(1. + ((sol0()) / (pi()))),(1. + ((sol0()) / (pi()))),15.53,(real_pow(4.,2.)),(real_pow(4.,2.))
};

  rectangle_total = rectangle(xmin,xmax);
  cout << "r: " << rectangle_total << endl;
  strategy s;
  setStrategy(xmin,xmax,s,1);  // this does the cases.
  //  setStrategy(xmin,xmax,s,0);

  {
  double data[4] = {1.0,4.0,2.0,3.0};
  assert(1.0==simplex2Dalpha(data,2));
  }

  {
  double data[4] = {1.0,4.0,3.0,2.0};
  assert(0.5==simplex2Dalpha(data,2));
  }

  {
    double data[8] = {0.99,10.0,1.0,9.0,11.0,12.0,9.0,1.0};
  assert(0.5==simplex2Dalpha(data,4));
  }

  global_alpha = 0.99915589538304627748 ;
  double y[6]={0.99999999999999988898,0.99999999999999988898,0.99999999999999988898,2.5195263290501368481,2.5195263290501368481,7.8392912459240529088};
  double r;
  t_varcombo(6,1,y,&r,0);
  
  cout.precision(30);
  cout << "alpha " << global_alpha << endl;
  cout << "combo " << r << endl;
  cout << "num1 " << numsgn(1.0,y,1) << endl;
  cout << "num2 " << numsgn(1.0,y,0) << endl;



}

