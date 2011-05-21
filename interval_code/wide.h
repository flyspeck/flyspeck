/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 2011-05-20                                                    */
/* ========================================================================== */

/*
A few locally constant (ie derivatives are all identically zero) lineIntervals.
When these are used, the allowDerivatives option should be disabled in recurse.cc.
 */

class wide
{

public:

	//////////
	// The calculation of D[taumar,y1] * Sqrt[delta] 
	//
  static interval mdtau_y(const domain&,const domain&);

	//////////
	// The calculation of D[taumar,{y1,2}]
	//
  static interval mdtau2_y(const domain&,const domain&);


	//////////
	// The calculation of delta_y as a locally constant function.
        // The domain is highly restricted, beware of implicit monotonicity assumptions!
	//
  static interval delta_y(const domain&,const domain&);

	//////////
	// Check the correctness of the linearization procedures.
	//
  static void selfTest();

};

