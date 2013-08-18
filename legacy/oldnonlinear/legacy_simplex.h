/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                           */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* Date: Moved from taylorData 2012-6-1                                      */
/* ========================================================================= */

// old version of taylorSimplex functions.
// used now for regression testing of new implementation.
// This is legacy code.

/*
CLASS
	legacy_simplex

	A library of static Functions of six variables.

OVERVIEW TEXT

	This class contains the most important Functions for
	sphere packings.  Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	Functions.

AUTHOR
	
	Thomas C. Hales
*/


class legacy_simplex
{
  public:
	//////////
	// reorder args f(x2,x3,x1,x5,x6,x2);
	//
 static Function rotate2(const Function&);

	//////////
	// reorder args f(x3,x1,x2,x6,x2,x5), etc.
	//
 static Function rotate3(const Function&);
 static Function rotate4(const Function&);
 static Function rotate5(const Function&);
 static Function rotate6(const Function&);


	//////////
	// unit is the constant function taking value 1.
	// x1,..,x6 are the squares of the edge lengths.
	// y1,...y6 are the edge lengths.
	// dih,dih2,dih3, are the dihedral angles along the first
	// three edges.
	// sol is the solid angle of a simplex
        // all of these are expressed in terms of the variables xi.
	//
 static const Function unit,x1,x2,x3,x4,x5,x6,
		y1,y2,y3,y4,y5,y6,
	  delta_x,delta_x4,x1_delta_x,delta4_squared_x,vol_x,sol,rad2,
	  dih,dih2,dih3,dih4,dih5,dih6,
	  ldih_x,ldih2_x,ldih3_x,ldih5_x,ldih6_x,
	  upper_dih_x,
	  eulerA_x,

	  rhazim_x,rhazim2_x,rhazim3_x,
	  gchi1_x,gchi2_x,gchi3_x,gchi4_x,gchi5_x,gchi6_x,
	  //	  marchalDih,marchalDih2,marchalDih3,
	  //    marchalDih4,marchalDih5,marchalDih6,
	  x1cube,x1square,
	  num1,num2,num_combo1,
	  rat1,rat2,den2,
	  edge_flat2_x,
	  edge_flat_x,
	  flat_term_x,
	  taum_x,
	  halfbump_x1, halfbump_x4;


	//////////
	// functions on an upright,flat,or quasiregular:
	// circumradius squared of the four faces of a simplex:
	// The circumradius squared of the face (ijk) of a simplex is eta2_ijk;
	// Miscellaneous functions.
	//
	static const Function eta2_126,eta2_135,eta2_234,eta2_456,
	  vol3_x_sqrt,
	  vol3f_x_lfun,
	  vol3f_x_sqrt2_lmplus,
	  arclength_x_123,
	  arclength_x_234,
	  arclength_x_126,
	  arclength_x_345,
	  norm2hh_x,
	  asn797k,asnFnhk,lfun_y1,
	  acs_sqrt_x1_d4,	  acs_sqrt_x2_d4;

	static const Function
	  sol_euler_x_div_sqrtdelta,
	  sol_euler345_x_div_sqrtdelta,
	  sol_euler156_x_div_sqrtdelta,
	  sol_euler246_x_div_sqrtdelta,
	  dih_x_div_sqrtdelta_posbranch,
	  dih2_x_div_sqrtdelta_posbranch,
	  dih3_x_div_sqrtdelta_posbranch,
	  dih4_x_div_sqrtdelta_posbranch,
	  dih5_x_div_sqrtdelta_posbranch,
	  dih6_x_div_sqrtdelta_posbranch,
	  ldih_x_div_sqrtdelta_posbranch,
	  ldih2_x_div_sqrtdelta_posbranch,
	  ldih3_x_div_sqrtdelta_posbranch,
	  ldih4_x_div_sqrtdelta_posbranch,
	  ldih5_x_div_sqrtdelta_posbranch,
	  ldih6_x_div_sqrtdelta_posbranch,
	  surf_x,
	  vol3r_126_x,

	  dih_x_126_s2,
	  dih2_x_126_s2,
	  dih3_x_126_s2,
	  dih4_x_126_s2,
	  dih5_x_126_s2,
	  dih6_x_126_s2,
	  ldih_x_126_s2,
	  ldih2_x_126_s2,
	  ldih6_x_126_s2,
	  dih_x_135_s2,
	  dih2_x_135_s2,
	  dih3_x_135_s2,
	  dih4_x_135_s2,
	  dih5_x_135_s2,
	  dih6_x_135_s2,
	  ldih_x_135_s2,
	  ldih3_x_135_s2,
	  ldih5_x_135_s2,
	  lfun_sqrtx1_div2 ,

	  delta_x_135_s2,
	  delta_x_126_s2,

	  vol3_x_135_s2, 

	  gamma3f_x_vLR_lfun,
	  gamma3f_x_vLR0,
	  gamma3f_x_vL_lfun,  gamma3f_x_vL0,
	  gamma3f_x_v_lfun,  gamma3f_x_v0,


	  // dec 29 , 2010:

	  ldih_x_126_n,
	  ldih2_x_126_n,
	  ldih6_x_126_n,
	  ldih_x_135_n,
	  ldih3_x_135_n,
	  ldih5_x_135_n,

          gamma3f_126_x_s_n,
	  gamma3f_135_x_s_n,
	  gamma3f_vLR_x_nlfun,
	  gamma3f_vLR_x_n0,
	  gamma3f_vL_x_nlfun,
	  gamma3f_vL_x_n0,

	  // may 2011:
	  tau_lowform_x,
	  tau_residual_x,
	  delta_y_LC,
	  mdtau_y_LC,
	  mdtau2_y_LC,
	  euler_3flat_x,
	  euler_2flat_x,
	  euler_1flat_x,
	  taum_3flat_x,
	  taum_2flat_x,
	  taum_1flat_x,
	  delta_pent_x,
          ell_uvx, // sep 2011.
	  ell_vx2,


	  // mar 2012, local optimality of bcc lattice
	  selling_volume2,
	  selling_surface_nn,
	  selling_surface_nn2_013,
	  selling_surface_nn01_23,
	  selling_homog,
	  fcc_ineq,
	  ;


	static const Function taum_x1(const interval&,const interval&);
	static const Function taum_x2(const interval&,const interval&);
	static const Function taum_x1_x2(const interval&);

	static const Function arclength_x1(const interval&,const interval&);
	static const Function arclength_x2(const interval&,const interval&);

	static const Function surfR126d(const interval&);


	static const Function /* legacy_simplex:: */ lindih(const interval& theta);

	static const Function /* legacy_simplex:: */ delta_126_x(const interval& x3s, const interval& x4s, const interval& x5s);

	static const Function /* legacy_simplex:: */ delta_234_x(const interval& x1s, const interval& x5s, const interval& x6s);

	static const Function /* legacy_simplex:: */ delta_135_x(const interval& x2s, const interval& x4s, const interval& x6s);

	static const Function /* legacy_simplex:: */ taum_sub1_x(const interval& x1s);

	static const Function /* legacy_simplex:: */ delta_sub1_x(const interval& x1s);

	static const Function /* legacy_simplex:: */ taum_sub246_x(const interval& x2s,const interval& x4s,const interval& x6s);

	static const Function /* legacy_simplex:: */ taum_sub345_x(const interval& x3s,const interval& x4s,const interval& x5s);

	//////////
	// Check the correctness of  routines.
	//
static void selfTest();

};
