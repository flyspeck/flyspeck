/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.
#ifndef RECURSE_H
#define RECURSE_H

#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
}
#include "error.h"
#include "interval.h"
#include "taylorInterval.h"

/* I'm in a verifying frenzy.  I'm not responding to outside noises.
	It's a heightened state of consciousness. S.McL.
*/


/*
CLASS
    cellOption
 
    A cellOption contains various parameter settings used to
	fine-tune the behavior of the recursive verification procedures in
	the class prove.
 
OVERVIEW TEXT
	The proof class is designed to prove many different inequalities
	in many different contexts.  It is necessary to customize 
	certain actions the recursive verification procedure.  This
	is done through various parameter settings.

AUTHOR
    Thomas C. Hales
*/

class cellOption {

public:
    enum X { silent, verbose };
    enum cellStatus { /*likely*/counterexample, cellPasses, inconclusive };

    // bailout options:
    int iterationCount;
    int iterationLimit;
    int recursionDepth;
    int timeout;    // in seconds.

    X printingMode;

    int startingIndex;
    double widthCutoff;
    int usingWidthCutoff;

    //////////
    // A lower bound (for quads) on the cross diagonal (default is 0).
    //
    double crossDiagMinEnclosed;
    double crossDiagMinDelta;

    //////////
    // Bounds on DeltaX[2,2,2,x1,x2,x6] and on DeltaX[2,2,2,x1,x3,x5].
    // Default = -1, means no bound.
    //
    double delta126Min;
    double delta126Max;
    double delta135Min;
    double delta135Max;

    // if set, then we may assume rad2(x1,x2,x3,x4,x5,x6)==2.
    int setRad2;

    //////////
    // Boolean flag for quads, to reduce to 8=4x2 extremal cases:
    // x8,x9 extremal, and if both are maximal then x7 is minimal (4 cases).
    // x1 or x5 is minimal (2 cases),
    int dimRedBackSym;

    // used in breaksapart to set threshhold.
    double margin;

    //////////
    // Allows a sharp inequality at some point without failing. 
    //
    int allowSharp;

    //////////
    // A cell passes if (partial f/partial x1 < 0).  The value of the function doesn't matter.
    // This can be useful in proving the monotonicity of certain functions.
    // There should only be one disjunct when this option is set.
    //
    int onlyCheckDeriv1Negative;

    // special code for the case 2065952723A.
    int strategy206A;
    
    //////////
    // 
    //
    //void setRecursionDepth(int rd) { recursionDepth=rd; }
    
    //////////
    // This only has an effect if it is positive.
    //
    //int getRecursionDepth() const { return recursionDepth; }
    
    //////////
    // quit after so many tries.
    //void setIterationLimit(int lim) { iterationLimit=lim; }
    
    //////////
    // 
    //int getIterationLimit() const { return iterationLimit; }
    
    //////////
    // 
    //void resetIterationCount() { iterationCount=0; }
    
    //////////
    //
    //int getIterationCount() const { return iterationCount; }
    
    //////////
    //
    //void augmentIterationCount() { iterationCount++; }

    //////////
    //
    //void setPrintMode(X u) { printingMode = u; }
    
    //////////
    //
    //X getPrintMode() { return printingMode; }
    
    //////////
    //
    cellOption() {  
      iterationCount=0;
      iterationLimit=0;
      recursionDepth=200;
      timeout=300000; // was 150000;

      printingMode=verbose; 

      startingIndex =0; 
      widthCutoff=0.05;
      usingWidthCutoff=0; 

      crossDiagMinEnclosed = 0.0;
      crossDiagMinDelta = 0.0;
  
      delta126Min= -1;
      delta126Max = -1;
      delta135Min = -1;
      delta135Max= -1;
      setRad2=0;

      dimRedBackSym=0;
      margin=0.0;
      allowSharp=0;
      onlyCheckDeriv1Negative=0;
  
      strategy206A=0;
    }
    
};




/*
CLASS
    prove

	Given a list of functions, prove that at least one is negative
	at every point of a given domain.
 
OVERVIEW TEXT
	This class gathers together a number of routines that
	take a taylorFunction (or more generally a list of taylorFunctions F)
	and proves that at least one of the functions F is negative
	on the given domain.

AUTHOR
    Thomas C. Hales
*/

class prove {
public:

	//////////
	// recursiveVerifier is the main inequality verification
	// procedure for simplices.  
	// It starts with a list of taylorFunctions I[],
	// and attempts to prove that at every point of the domain
	// x--z, at least one of the functions is negative.
	// Start with depth=0.  Each step of the recursion will
	// increase the depth by 1.
	// Start with x=x0, z=z0.  As the domain is subdivided,
	// x will increase and z will decrease.  x0, z0 remain fixed,
	// unless there is dimension reduction.
	//
static int recursiveVerifier(int depth,
	const domain& x,const domain& z,     /// current cell
	const domain& x0,const domain& z0,   // boundary
	const taylorFunction* I[],
	int count,cellOption& options);

	//////////
	// recursiveVerifierQ is the main inequality verification
	// procedure for quad clusters.
	// Each quad cluster is divided into two simplices A,B along
	// the shortest diagonal.  A list of taylorFunctions is
	// given IA, IB for the two simplices.  The recursiveVerifierQ
	// procedure attempts to show that at every point in the domain
	// xA--zA (on A), xB--zB (on B), there is an index for which
	// the sum of the values of IA[index] on A and IB[index] on B
	// is negative.  IA[index] or IB[index] is allowed to be positive
	// as long as the sum is negative.  Dimension reduction is
	// always used in recursiveVerifierQ.  Otherwise the dimensions
	// are too great to be handled by computer.  This means that
	// if unreducible taylorFunctions are used, the
	// results are unreliable.  
	//
	// The depth starts out at 0.
	//
static int recursiveVerifierQ(int depth, 
	const domain& xA,const domain& xB,
	const domain& zA,const domain& zB,
	const taylorFunction* IA[],const taylorFunction* IB[],int Nineq,
	cellOption& options);


};

#endif
