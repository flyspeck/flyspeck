/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifdef LINEINTERVAL_H
#ifndef LINEINTERVAL_INLINE_H
#define LINEINTERVAL_INLINE_H

inline double lineInterval::hi() const { return interMath::sup(f); }
inline double lineInterval::low() const { return interMath::inf(f); }

inline double domain::getValue(int i) const { return ( ((i<6)&&(i>=0)) ? x[i] :
		(error::message("face out of range"), 0) );  }






#endif
#endif
