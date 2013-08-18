/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                           */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* Date: Moved from taylorData 2012-6-1                                      */
/* ========================================================================= */


/*
CLASS
	Lib

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


class Lib
{

 public:

  static const univariate i_halfbump_x,i_gchi,i_flat_term_x,
    i_lfun,i_rho;

    static const univariate i_gamma2_x_div_azim_v2(const interval&);

  static const Function promote1_to_6(const univariate&);

  static const Function constant6(const interval&);


 static Function uni(const univariate&,const Function&);


	//////////
	// unit is the constant function taking value 1.
	// x1,..,x6 are coordinate projections.
	// y1,...y6 are sqrts of x1,..x6.
	// dih_x dihedral angle along the first edge.
	// sol_x is the solid angle.
        // rad2_x is the circumradius square of a simplex.
        // all of these are expressed in terms of the variables xi.
	//
  static const Function 
    x1,x2,x3,x4,x5,x6,y1;

  static const Function unit,two6,edge_flat2_x,halfbump_x1,eta2_126,ups_126,
    delta_x,delta_x4,dih_x,sol_x,rad2_x,
    num1;

   static void selfTest();

};
