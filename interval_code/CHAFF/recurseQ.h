//  copyright (c) 1997, Thomas C. Hales, all rights reserved.
#ifndef RECURSE_Q
#define RECURSE_Q

#include <iomanip.h>
#include <iostream.h>
extern "C"
{
#include <math.h>
#include <stdlib.h>
}
#include "error.h"
#include "interval.h"
#include "taylorInterval.h"

void recursive_verifierQ(int depth, // case sym=0 of proto
                const double xA[6],const double xB[6],  
                const double zA[6],const double zB[6],   
                const ineq IA[],const ineq IB[],int Nineq);

//obsolete: (use skipcases instead)
void recursive_verifierQsym(int depth, // case sym=1 of proto
                const double xA[6],const double xB[6],  
                const double zA[6],const double zB[6],   
                const ineq IA[],const ineq IB[],int Nineq);

//obsolete: (use skipcases instead)
void recursive_verifierQproto(int depth,
                const double xA[6],const double xB[6],     /// current cell
                const double zA[6],const double zB[6],   // boundary
                const ineq IA[],const ineq IB[],int Nineq,int sym);

void skipcases(const int skiplist[],int len); // skip R-cases.
void setWCUTOFF(double x); // restrict WCUTOFF below 0.3.
#endif
