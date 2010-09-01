//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


#include <iomanip.h>
#include <float.h>

//#include <iostream.h>
extern "C"
{
#include <math.h>
//#include <stdlib.h>
}
#include "error.h"
#include "interval.h"
#include "taylorInterval.h"
#include "recurse.h"


static const int MAXcount = 4; // MAX number of taylorFunctions in an array.
/*
static inline double dabs(interval x)
	{
	return interMath::sup(interMath::max(x,-x));	
	}
*/
static double max(const double x[6])
	{
	double t=x[0];
	for (int i=0;i<6;i++) if (x[i]>t) t = x[i];
	return t;
	}

static double max(double x,double y)
	{
	return x > y ? x : y;
	}

static double min(double x,double y)
	{
	return y > x ? x : y;
	}

static void centerform
	(const double x[6],const double z[6],double y[6],double w[6])
	{ // y = center of Taylor expansion = approximate center.
	interMath::up();
	for (int i=0;i<6;i++)
		{
		y[i]= (z[i]+x[i])/2.0;
		w[i]= max(z[i]-y[i],y[i]-x[i]); //up-mode required.
		}
	}

static int unreduced(const double x[6],const double z[6])
	{
	int t;
	t = (
		   ((z[0]==x[0])&&(z[3]==x[3])) 
		|| ((z[1]==x[1])&&(z[4]==x[4]))
		|| ((z[2]==x[2])&&(z[5]==x[5]))
		|| ((z[3]==x[3])&&(z[4]==x[4]))
		|| ((z[3]==x[3])&&(z[5]==x[5]))
		|| ((z[4]==x[4])&&(z[5]==x[5]))
		|| ((z[0]==x[0])&&(z[1]==x[1])&&(z[2]==x[2]))
	     );
	return (!t);
	}

static int setreduction(int i,const double x[6],const double z[6],
	const double x0[6], double zz[6])
	// return false if the reduction flows out of the cell.
	// else true;
	{
	int j;
	for (j=0;j<6;j++) zz[j]=z[j];
	switch (i)
		{
		case 0 : if ((x[0]>x0[0])||(x[3]>x0[3])) return 0; 
			 zz[0]=x[0]; zz[3]=x[3];
			 break;
		case 1 : if ((x[1]>x0[1])||(x[4]>x0[4])) return 0; 
			 zz[1]=x[1]; zz[4]=x[4];
			 break;
		case 2 : if ((x[2]>x0[2])||(x[5]>x0[5])) return 0; 
			 zz[2]=x[2]; zz[5]=x[5];
			 break;
		case 3 : if ((x[3]>x0[3])||(x[4]>x0[4])) return 0; 
			 zz[3]=x[3]; zz[4]=x[4];
			 break;
		case 4 : if ((x[3]>x0[3])||(x[5]>x0[5])) return 0; 
			 zz[3]=x[3]; zz[5]=x[5];
			 break;
		case 5 : if ((x[4]>x0[4])||(x[5]>x0[5])) return 0; 
			 zz[4]=x[4]; zz[5]=x[5];
			 break;
		case 6 : if ((x[0]>x0[0])||(x[1]>x0[1])||(x[2]>x0[2])) 
			 return 0; 
			 zz[0]=x[0]; zz[1]=x[1]; zz[2]=x[2];
			 break;
		default : error::message("setreduction out of range");
		}
	return 1;
	}

static int reducible(const taylorFunction* I[],int count)
	{
	for (int i=0;i<count;i++)
		if (!I[i]->getReducibleState()) return 0;
	return 1;
	}


static void report_failure(const double x[6],const double z[6],const char* s)
	{
	static const int MAXFAIL=25;
	static int fail_count=0;
	cout.precision(20);
	int i;
	interMath::down();
	cout << "\n{" << flush;
	for (i=0;i<6;i++) cout << x[i] << (i<5?",":"} ")  << flush;
	interMath::up();
	cout << "{" << flush;
	for (i=0;i<6;i++) cout << z[i] << (i<5?",":"} ")  << flush;
	cout << " " << flush;
	cout << s << endl << flush;
	if (fail_count++> MAXFAIL)
		{ error::message("too many exceptions; bailing out");
		  exit(0);
		}
	cout << flush;
	}

static double deltainf(double x1,double x2,double x3,double x4,double x5,
        double x6)
        {
        interMath::down();
        return
         ((-x2)*x3)*x4 +((- x1)*x3)*x5 +((- x1)*x2)*x6 +((- x4)*x5)*x6 +
   x3*(x1 + x2 + x4 + x5)*x6 +  (x3*(-x3-x6))*x6 +
   x2*x5*(x1 + x3 + x4 + x6) + x2*(x5*(-x2-x5)) +
        x1*x4*(x2 + x3 + x5 + x6)+ x1*(x4*(-x1-x4));
        }

static inline int sgn(interval x) 
	{ if (interMath::inf(x)>0.0) return 1;
			else if (interMath::sup(x)<0.0) return -1; else return 0;
	}

static int sameSgn(const lineInterval& x,const lineInterval& y)
	{
	for (int i=0;i<6;i++) if (sgn(x.partial(i))!=sgn(y.partial(i))) return 0;
	return 1;
	}

static void resetBoundary(double x0[6],double z0[6],
	const double x[6],const double z[6])
	{
	for (int i=0;i<6;i++) { x0[i]=x[i]; z0[i]=z[i]; }
	}

static void deleteFunction(const taylorInterval* T[],const taylorFunction* I[],
	int& count,int i)
	{
	count--; if (count<0) error::message("unexpected negative number");
	int j;
	for (j=i;j<count;j++)
		{ T[j]=T[j+1];  I[j]=I[j+1]; }
	}

static void moveFirst(const taylorInterval* T[],const taylorFunction* I[],int i)
	{
	if (i>0) { T[0]=T[i];  I[0]=I[i]; }
	}


static cellOption::cellStatus
	verifyCell(double x[6],double z[6],double x0[6],double z0[6],
		const taylorFunction* I[],int& count,
		cellOption options)
	{
	if (count>MAXcount) 
		{
		cout << "There are " << count << " inequalities." << endl;
		error::message("In verifyCell, increase MAXcount and recompile");
		return cellOption::inconclusive;
		}

	taylorInterval dih;	 // a pseudo-inequality
	if (options.isUsingDihMax()) 
		{
		double x4max;
		if (edgeBound::x4_upper_from_dih_upper(x,z,options.getDihMax(),x4max))
			{
			if (x4max<x[3]) return cellOption::cellPasses; // empty range.
			if (z[3]>x4max) z[3] = x4max;
			if (deltainf(z[0],x[1],x[2],z[3],x[4],x[5])<=0.0) 
				return cellOption::inconclusive;
			dih = taylorSimplex::dih.evalf(domain(x),domain(z));
			}
		}

	taylorInterval eta;	 // a pseudo-inequality.
	if (options.isUsingBigFace126())
		{
		taylorInterval eta = taylorSimplex::eta2_126.evalf(domain(x),domain(z));
		if ((eta.isValidData()) && (eta.upperBound()<2.0))
			 return cellOption::cellPasses; //empty range.
		}

	// deltainf is not intended to catch everything, just main negativities
	if (deltainf(z[0],x[1],x[2],z[3],x[4],x[5])<=0.0) 
		return cellOption::inconclusive;

	/* GOING STRONG LOOP*/
	int i,j;
	const taylorInterval* T[MAXcount];
	taylorInterval  Target[MAXcount];
	int goingstrong=1;
	double maxwidth=1;
	while (goingstrong--)
	{

	/*exit if delta might be negative*/ {
	double y[6],w[6];
	centerform(x,z,y,w); 
	if (deltainf(y[0],y[1],y[2],y[3],y[4],y[5])<=0.0) 
		return cellOption::inconclusive;
	maxwidth = max(w); 
	}

	/*pass cell if some taylor bound holds*/{
	for (i=0;i<count;i++)
		{
		Target[i]= I[i]->evalf(domain(x),domain(z)); 
		T[i]=&Target[i];
		if (!(T[i]->isValidData())) return cellOption::inconclusive;
		if (T[i]->upperBound()<0.0) return cellOption::cellPasses;
		}
	}

	/*report zero width cells */ {
	static const double epsilon_width = 1.0e-8;
	if (maxwidth < epsilon_width) 
		{
		if (options.getPrintMode()==cellOption::silent) 
			return cellOption::counterexample; 
		report_failure(x,z,"isolated point");
		cout.precision(20);
		for (i=0;i<count;i++)
			{
			interMath::down();
			cout << "  value=[" << T[i]->lowerBound() << flush;
			interMath::up();
			cout << "," << T[i]->upperBound() << "]\n" << flush;
			}
		cout << flush;
		return cellOption::counterexample;
		}
	}

	/*delete false inequalities */{
	i=0; while (i<count)
		{
		if (T[i]->lowerBound() > 0.0)
			{
			resetBoundary(x0,z0,x,z);
			deleteFunction(T,I,count,i); //it decrements count; 
			}
		else i++;
		}
	if (count==0) 
		{
		if (options.getPrintMode()==cellOption::silent) 
			return cellOption::counterexample; 
		report_failure(x,z,"current inequalities are false");
		return cellOption::counterexample;
		}
	}

	/* do derivatives. */{
	for (i=0;i<6;i++) if (x[i]<z[i])
		{
		int allpos=1, allneg=1;
		for (j=0;j<count;j++) if (T[j]->lowerPartial(i)<0.0) allpos=0;
		for (j=0;j<count;j++) if (T[j]->upperPartial(i)>0.0) allneg=0;

		if ((options.isUsingDihMax())&&(allpos+allneg>0))
			{
			// don't flow through the dihMax.
			if (!dih.isValidData()) { allpos=allneg=0; }
			else if ((dih.upperBound()> options.getDihMax())&&
				 dih.lowerBound()< options.getDihMax())
				{
				allpos=allneg=0;
				}
			}

		if (options.isUsingBigFace126())
			{
			// treat the pseudo-inequality eta2- 2 < 0 :
			if (!eta.isValidData()) { allpos=allneg=0; }
			else if ((eta.upperBound()> 2.0)&&
				(eta.lowerBound()<2.0)) { allpos=allneg=0;}
			}

		if (allpos)
			{
			if (z[i]<z0[i]) return cellOption::cellPasses; // slide off the edge.
			else { z0[i]=x0[i]=x[i]=z[i]; goingstrong=1; }
			}
		else if (allneg)
			{
			if (x[i]>x0[i]) return cellOption::cellPasses;
			else { x0[i]=z0[i]=z[i]=x[i]; goingstrong=1; }
			}
		}
	}

	} // end while goingstrong
 

	// now drop the numerically false inequalities;
	static const double WCUTOFF = 0.05;
	int mixedsign;
	double yyn[6],yu[6];  // look at the lowest & highest corners
	lineInterval cn,cu;
	if (maxwidth<WCUTOFF)
	{
	i=0; while (i<count) if (T[i]->center().low() >0.0)
		{
		mixedsign=0;
		for (j=0;j<6;j++)
			{
			yyn[j]= (sgn(T[i]->center().partial(j)) >0 ? x[j] : z[j]);
			yu[j]= (sgn(T[i]->center().partial(j))> 0 ? z[j] : x[j]);
			if (sgn(T[i]->center().partial(j))==0) mixedsign = 1;
			}
		if (mixedsign) { mixedsign=0; i++; continue; }
		cn = I[i]->evalAt(domain(yyn)); cu= I[i]->evalAt(domain(yu));
		if ((min(cn.low(),cu.low())>0.0)&&
			(sameSgn(T[i]->center(),cn))&&
			sameSgn(T[i]->center(),cu))
			{
			deleteFunction(T,I,count,i); 
			resetBoundary(x0,z0,x,z);
			}
		else i++;
		}
		else i++;
	}
	if (count==0) 
		{
		if (options.getPrintMode()==cellOption::silent) return cellOption::counterexample; 
		report_failure(x,z,"current inequalities are doubtful");
		return cellOption::counterexample;
		}

	// now keep a single numerically true inequality.
	if ((maxwidth<WCUTOFF)&&(count>1))
	{
	double margin =0.0;
	for (i=0;i<count;i++) if (T[i]->center().hi()< 0.0)
		{
		mixedsign=0;
		for (j=0;j<6;j++)
			{
			yyn[j]= (sgn(T[i]->center().partial(j))>0 ? x[j] : z[j]);
			yu[j]= (sgn(T[i]->center().partial(j))>0 ? z[j] : x[j]);
			if (sgn(T[i]->center().partial(j))) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		cn = I[i]->evalAt(domain(yyn)); cu= I[i]->evalAt(domain(yu));
		if ((max(cn.hi(),cu.hi())< -margin)&&
			(sameSgn(T[i]->center(),cn))&&sameSgn(T[i]->center(),cu))
			{
			margin = -max(cn.hi(),cu.hi());
			if (i) 
				{
				moveFirst(T,I,i);
				resetBoundary(x0,z0,x,z);
				}
			}
		}
	if (margin>0.0) count =1; // Disregard the rest of the inequalities;
	} // if max(w) 
	return cellOption::inconclusive;
	} // end verifyCell.





static int count(int i,int j)
	{
	return (0 == (i % j));
	}

void stats()
	{
	static int statcounter=0;
	static int linefeed=0;
	if (count(statcounter++,1000000)) 
		{
		cout << "[" << statcounter/1000000 << "]" << flush;
						//6/12/97, was 10^5
		if (count(linefeed++,10) )
			{
			cout << " " << flush; 
			error::printTime();
			}
		}
	}

int prove::recursiveVerifier(int depth,
		const domain& xD,const domain& zD,     /// current cell
		const domain& x0D,const domain& z0D,   // boundary
		const taylorFunction* I[],
		int count,cellOption& options)
	// function should not change any of these parameters.
	// except iterationCount in options.
	{
	double x[6],z[6];     /// current cell
	double x0[6],z0[6]; 
	int i;
	for (i=0;i<6;i++)
		{
		x[i]=xD.getValue(i); z[i]=zD.getValue(i);
		x0[i]=x0D.getValue(i); z0[i]=z0D.getValue(i);
		}
	stats(); 
	options.augmentIterationCount();
	if ((options.getIterationLimit()>0)&&
		(options.getIterationLimit()<options.getIterationCount()))
		{
		report_failure(x,z,"iteration limit exceeded");
		cout << "iteration limit is set at " << options.getIterationLimit() << endl;
		return 0;
		}
	if ((options.getChiShortCut())&&
		(edgeBound::chi234min(domain(x),domain(z)) >0.0)) return 1;
	int MAXDEPTH = 20;
	if (options.getRecursionDepth()>0) MAXDEPTH = options.getRecursionDepth();
	if (depth++ > MAXDEPTH) 
		{
		report_failure(x,z,"recursion limit exceeded");
		cout << "recursion depth is currently at " << MAXDEPTH << endl;
		return 0;
		}
	if ((reducible(I,count) )&&(unreduced(x,z)))
		{
		double zz[6];
		for (i=0;i<7;i++) if (setreduction(i,x,z,x0,zz))
			{
			if (!recursiveVerifier(depth,x,zz,x0,z0,I,count,
				options)) return 0;
			};
		return 1;
		}
	// make a backup. verifyCell changes the parameters.
	double xx[6],zz[6],xx0[6],zz0[6];
	for (i=0;i<6;i++) 
		{xx[i]=x[i];zz[i]=z[i];xx0[i]=x0[i];zz0[i]=z0[i];}
	if (count>MAXcount) 
		{
		cout << "There are " << count << " inequalities in use."
			 << endl << flush;
		error::message("Change the parameter MAXcount and recompile");
		return 0;
		}
	const taylorFunction* II[MAXcount];
	for (i=0;i<count;i++) II[i]=I[i]; 
	int Ncount = count;
	// Here is the main line of the procedure.  Check if it verifies.
	cellOption::cellStatus v =verifyCell(xx,zz,xx0,zz0,II,Ncount,
			options);// xx,zz,.. affected.
	if (v==cellOption::counterexample) return 0; 
	else if (v==cellOption::cellPasses) return 1; 
	// hence (v==cellOption::inconclusive)
	
	// Continue by starting the recursion;
	interMath::up();
	double y[6]; for (i=0;i<6;i++) y[i]= (xx[i]+zz[i])/2.0; // ~ center.
	double xr[6],zr[6];
	static const double epsilon_width = 1.0e-8;
	for (i=0;i<6;i++) { xr[i]=xx[i]; zr[i]=zz[i]; }
	int imax[6],iter[6];
	for (i=0;i<6;i++) { imax[i]= ( zz[i]>xx[i]+epsilon_width? 2 : 1 ); }
	double w0=zz[0]-xx[0]; 
	for (i=1;i<6;i++) 
		if (w0<zz[i]-xx[i]) w0=zz[i]-xx[i]; 
	w0 = w0/2.0; //  approximate width;
	for (i=0;i<6;i++) if ((imax[i]>1)&&(zz[i]-xx[i]<w0)) imax[i]=1;
	for (iter[0]=0;iter[0]<imax[0];iter[0]++)  // at most 2^6 cases
	for (iter[1]=0;iter[1]<imax[1];iter[1]++)
	for (iter[2]=0;iter[2]<imax[2];iter[2]++)
	for (iter[3]=0;iter[3]<imax[3];iter[3]++)
	for (iter[4]=0;iter[4]<imax[4];iter[4]++)
	for (iter[5]=0;iter[5]<imax[5];iter[5]++)
		{
		for (i=0;i<6;i++) xr[i] = ( iter[i] ? y[i] : xx[i] );
		for (i=0;i<6;i++) zr[i] = ( imax[i]-iter[i]-1? y[i] : zz[i] );
		if (!recursiveVerifier(depth,xr,zr,xx0,zz0,II,Ncount,
			options)) return 0;
		}
	return 1;
	}





/**********************************************

				START of QUAD CLUSTER MATERIAL 

***********************************************/

static int fitstogether(const double x[6],const double y[6])
	{
	return ((x[1]==y[1])&&(x[2]==y[2])&&(x[3]==y[3]));
	}

static int unreducedQ(const double xA[6],const double xB[6],
	const double zA[6],const double zB[6])
	{
	int t;
	t = (
		   ((zA[4]==xA[4])&&(zB[5]==xB[5])) 
		|| ((zA[5]==xA[5])&&(zB[4]==xB[4]))
		|| ((zA[4]==xA[4])&&(zB[4]==xB[4])&&(zA[1]==xA[1]))
		|| ((zA[5]==xA[5])&&(zB[5]==xB[5])&&(zA[2]==xA[2]))
		|| ((zA[4]==xA[4])&&(zA[5]==xA[5])&&(zB[0]==xB[0]))
		|| ((zB[4]==xB[4])&&(zB[5]==xB[5])&&(zA[0]==xA[0]))
		|| ((zA[0]==xA[0])&&(zA[1]==xA[1])&&(zB[4]==xB[4]))
		|| ((zA[0]==xA[0])&&(zA[2]==xA[2])&&(zB[5]==xB[5]))
		|| ((zB[0]==xB[0])&&(zB[2]==xB[2])&&(zA[5]==xA[5]))
		|| ((zB[0]==xB[0])&&(zB[1]==xB[1])&&(zA[4]==xA[4]))
		|| ((zB[0]==xB[0])&&(zB[1]==xB[1])&&(zB[2]==xB[2])&&
				(zA[0]==xA[0])) // case 10
		|| ((zA[4]==xA[4])&&(zB[4]==xB[4])&&(zB[3]==xB[3]))
		|| ((zA[5]==xA[5])&&(zB[5]==xB[5])&&(zB[3]==xB[3])) //12
		|| ((zB[3]==xB[3])&&(zB[0]==xB[0])&&(zA[4]==xA[4])) //13
		|| ((zB[3]==xB[3])&&(zB[0]==xB[0])&&(zA[5]==xA[5])) //14
		|| ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[4]==xB[4])) //15
		|| ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[5]==xB[5])) //16
		|| ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[0]==xB[0])) //17
	     );
	return (!t);
	}

static int setreductionQ(int i,const double xA[6],const double xB[6],
		const double zA[6],const double zB[6],
		double zzA[6],double zzB[6])
	// return false if the reduction flows out of the cell.
	// else true;
	{
	int j;
	for (j=0;j<6;j++) { zzA[j]=zA[j]; zzB[j]=zB[j]; }
	switch (i)
		{
		case 0 : zzA[4]=xA[4]; zzB[5]=xB[5]; break;
		case 1 : zzA[1]=zzB[1]=xA[1]; zzA[4]=xA[4]; zzB[4]=xB[4]; break;
		case 2 : zzA[4]=xA[4]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
		case 3 : zzA[0]=xA[0]; zzB[4]=xB[4]; zzB[5]=xB[5]; break;
		case 4 : zzA[0]=xA[0]; zzA[1]=zzB[1]=xA[1]; zzB[4]=xB[4]; break;
		case 5 : zzA[1]=zzB[1]=xA[1]; zzA[4]=xA[4]; zzB[0]=xB[0]; break;
		case 6 : zzA[0]=xA[0]; zzA[1]=zzB[1]=xA[1]; 
			  zzA[2]=zzB[2]=xA[2]; zzB[0]=xB[0]; break;
		case 7 : zzA[5]=xA[5]; zzB[4]=xB[4]; break;
		case 8 : zzA[2]=zzB[2]=xA[2]; zzA[5]=xA[5]; zzB[5]=xB[5]; break;
		case 9 : zzA[0]=xA[0]; zzA[2]=zzB[2]=xA[2]; zzB[5]=xB[5]; break;
		case 10: zzA[2]=zzB[2]=xA[2]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
		case 11: zzA[3]=zzB[3]=xA[3]; zzA[4]=xA[4]; zzB[4]=xB[4]; break;
		case 12: zzA[3]=zzB[3]=xA[3]; zzA[5]=xA[5]; zzB[5]=xB[5]; break;
		case 13: zzA[3]=zzB[3]=xA[3]; zzA[4]=xA[4]; zzB[0]=xB[0]; break;
		case 14: zzA[3]=zzB[3]=xA[3]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
		case 15: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[4]=xB[4]; break;
		case 16: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[5]=xB[5]; break;
		case 17: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[0]=xB[0]; break;
		default : error::message("setreductionQ out of range");
		}
	return 1;
	}

static int sameSgnQ(const lineInterval& cA,const lineInterval& cB,
	const lineInterval& dA,const lineInterval& dB)
	{
	int k[3]={0,4,5},i;
	for (i=0;i<3;i++) 
		if (sgn(cA.partial(k[i]))!=sgn(dA.partial(k[i]))) return 0;
	for (i=0;i<3;i++) 
		if (sgn(cB.partial(k[i]))!=sgn(dB.partial(k[i]))) return 0;
	for (i=1;i<4;i++) 
		if (sgn(cA.partial(i)+cB.partial(i))!=
			sgn(dA.partial(i)+dB.partial(i))) return 0;
	return 1;
	}

static void deleteIneqQ(const taylorInterval* tA[],const taylorInterval* tB[],
	const taylorFunction* IA[],const taylorFunction* IB[],int& Nineq,int i)
	{
	Nineq--; if (Nineq<0) error::message("unexpected negative numberQ");
	int j;
	for (j=i;j<Nineq;j++)
		{ tA[j]=tA[j+1];  IA[j]=IA[j+1]; 
		  tB[j]=tB[j+1];  IB[j]=IB[j+1]; }
	}

static void printit(const double x[6])
        {
        cout.precision(8); interMath::nearest();
        for (int i=0;i<6;i++) cout << x[i] << " " << flush;
        cout << endl << flush;
        }

static int verifyCellQ(double xA[6],double xB[6],double zA[6],double zB[6],
		const taylorFunction* IA[],const taylorFunction* IB[],
		int& Nineq,cellOption& option)
	// return true if all verifies or if all counterexamples have been
	// 	properly reported.
	//return false if x,z ... require further investigation.
	{
	if (!fitstogether(xA,xB))
		{
		error::message("Qx-mismatch"); printit(xA); printit(xB); return 0;
		}
	if (!fitstogether(zA,zB))
		{
		error::message("Qz-mismatch"); printit(zA); printit(zB); return 0;
		}
	// get out if delta is possibly negative.
	if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<=0.0) return 0;
	if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.0) return 0;
	double yA[6],yB[6],wA[6],wB[6]; 
	const taylorInterval* tA[MAXcount];
	const taylorInterval* tB[MAXcount]; 
	taylorInterval targetA[MAXcount];
	taylorInterval targetB[MAXcount];
	if (Nineq>MAXcount) 
		{
		cout << "There are " << Nineq << " inequalities." << endl;
		error::message("Update MAXcount in verifyCellQ");
		return 0;
		}
	int i,j;
	// get out fast if any of the crude taylor bounds hold.
	for (i=0;i<Nineq;i++)
		{
		targetA[i]= IA[i]->evalf(xA,zA);
		tA[i]=&targetA[i];
		if (!tA[i]->isValidData()) return 0;
		targetB[i]= IB[i]->evalf(xB,zB);
		tB[i]=&targetB[i];
		if (!tB[i]->isValidData()) return 0;
		if (taylorInterval::upperboundQ(*tA[i],*tB[i])< 0.0) return 1;
		}
 
	centerform(xA,zA,yA,wA); 
	centerform(xB,zB,yB,wB); 
	static const double epsilon_width = 1.0e-8;
	if (max(max(wA),max(wB)) < epsilon_width) 
		{
		report_failure(xA,zA,"A:isolated point");
		report_failure(xB,zB,"B:isolated point");
		cout.precision(20);
		for (i=0;i<Nineq;i++)
			{
			interMath::down();
			cout << "  value=[A:" << tA[i]->lowerBound() << flush;
			interMath::up();
			cout << "," << tA[i]->upperBound() << "]" << flush;
			interMath::down();
			cout << "  [B:" << tB[i]->lowerBound()  << flush;
			interMath::up();
			cout << "," << tB[i]->upperBound() << "]\n" << flush;
			}
		cout << flush;
		return 1;
		}
	i=0; while (i<Nineq)
		{
		if (taylorInterval::lowerboundQ(*tA[i],*tB[i]) > 0.0)
			{
			deleteIneqQ(tA,tB,IA,IB,Nineq,i); 
				//it decrements Nineq; 
			}
		else i++;
		}
	if (Nineq==0) 
		{
		report_failure(xA,zA,"A:current inequalities are false");
		report_failure(xB,zB,"B:current inequalities are false");
		return 1;
		}
 
	// now keep a single numerically true inequality.
	double WCUTOFF = 0.3;
	if (max(zA[0],zB[0])>6.00) WCUTOFF=0.1; // things are unstable here!
	if (option.hasWidthCutoff()) WCUTOFF=option.getWidthCutoff(); // patch 6/26/97
	int s;
	if ((max(max(wA),max(wB))<WCUTOFF)&&(Nineq>1))
	{
	double yAn[6],yAu[6],yBn[6],yBu[6];
		// look at the lowest & highest corners
	int k[3]={0,4,5};
	lineInterval tAn,tAu,tBn,tBu;
	int mixedsign;
	double margin =0.0;
	for (i=0;i<Nineq;i++) 
	if (interMath::up(), tA[i]->center().hi()+tB[i]->center().hi()< 0.0)
		{
		mixedsign=0;
		for (j=0;j<3;j++)
			{
			s = sgn(tA[i]->center().partial(k[j]));
			yAn[k[j]]= (s>0 ? xA[k[j]]: zA[k[j]]);
			yAu[k[j]]= (s>0 ? zA[k[j]]: xA[k[j]]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		for (j=0;j<3;j++)
			{
			s = sgn(tB[i]->center().partial(k[j]));
			yBn[k[j]]= (s>0 ? xB[k[j]]: zB[k[j]]);
			yBu[k[j]]= (s>0 ? zB[k[j]]: xB[k[j]]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		for (j=1;j<4;j++)
			{
			s = sgn(tB[i]->center().partial(j)
					+tA[i]->center().partial(j));
			yAn[j]=yBn[j]= (s>0 ? xB[j]: zB[j]);
			yAu[j]=yBu[j]= (s>0 ? zB[j]: xB[j]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		tAn = IA[i]->evalAt(yAn); tAu= IA[i]->evalAt(yAu);
		tBn = IB[i]->evalAt(yBn); tBu= IB[i]->evalAt(yBu);
		if ((min(-tAn.hi()-tBn.hi(),-tAu.hi()-tBu.hi()) > margin)
			&&(sameSgnQ(tA[i]->center(),tB[i]->center(),tAn,tBn))
			&&(sameSgnQ(tA[i]->center(),tB[i]->center(),tAu,tBu)))
			{
			margin = min(-tAn.hi()-tBn.hi(),-tAu.hi()-tBu.hi());
			moveFirst(tA,IA,i);
			moveFirst(tB,IB,i);
			}
		}
	if (margin>0.0) Nineq =1; // Disregard the rest of the inequalities;
	} // if max(w) 
	return 0;
	} // end verifyCellQ.


static int breaksapart(int depth,
	const double xA[6],const double xB[6],
	const double zA[6],const double zB[6],
	const taylorFunction* IA[],const taylorFunction* IB[],int Nineq)
	{
	static const interval zero("0");
	static const interval two("2");
	if (Nineq<1) error::message("Lacking in inequalities");
	if (Nineq>1) return 0;
	if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<=0.0) return 0;
	if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.0) return 0;
	double yA[6],yB[6],wA[6],wB[6],yAn[6],yBn[6],yAu[6],yBu[6];
	lineInterval tA,tB,tAu,tBu,tAn,tBn;
	centerform(xA,zA,yA,wA);
	centerform(xB,zB,yB,wB);
	tA=IA[0]->evalAt(yA);
	tB=IB[0]->evalAt(yB);
	double WCUTOFF=0.3;
	if (max(zA[0],zB[0])>6.00) WCUTOFF=0.1; // things are unstable here!
	if (max(max(wA),max(wB)) >WCUTOFF) return 0;
	int j,u,sgnA[6],sgnB[6],k[6]={1,2,3,0,4,5};
	for (j=0;j<6;j++)
		{
		u = k[j];
		sgnA[u] = sgn(tA.Df[u] + (j<3 ? tB.Df[u] : zero ) );
		if (sgnA[u]==0) return 0;
		yAn[u]= (sgnA[u]>0 ? xA[u] : zA[u]);
		yAu[u]= (sgnA[u]>0 ? zA[u] : xA[u]);
		sgnB[u] = sgn(tB.Df[u] + (j<3 ? tA.Df[u] : zero ) );
		if (sgnB[u]==0) return 0;
		yBn[u]= (sgnB[u]>0 ? xB[u] : zB[u]);
		yBu[u]= (sgnB[u]>0 ? zB[u] : xB[u]);
		}
	tAn=IA[0]->evalAt(yAn); tAu=IA[0]->evalAt(yAu);
	tBn=IB[0]->evalAt(yBn); tBu=IB[0]->evalAt(yBu);
	if (!(sameSgnQ(tA,tB,tAn,tBn))) return 0;
	if (!(sameSgnQ(tA,tB,tAu,tBu))) return 0;
	interval e,eps[6];
	e = (tAu.f - tBu.f)/two;
	for (j=0;j<6;j++) eps[j]= (tAu.Df[j]-tBu.Df[j])/two;
	// test these values;
	if ((interMath::sup(tAu.f)> interMath::inf(e)) ||
		(interMath::sup(tAn.f)> interMath::inf(e)) ||
		(interMath::sup(tBu.f)> interMath::inf(-e)) ||
		(interMath::sup(tBn.f)> interMath::inf(-e)) ||
		(interMath::sup(tAn.f+tBn.f)>interMath::sup(tA.f+tB.f)) ||
		(interMath::sup(tA.f+tB.f)>interMath::sup(tAu.f+tBu.f))
			) return 0;
	interval iyAu1(yAu[1],yAu[1]),iyAu2(yAu[2],yAu[2]),iyAu3(yAu[3],yAu[3]);
	// T is the linear bound on A at yAu:
	taylorFunction T = taylorSimplex::unit*e +
		(taylorSimplex::x2+taylorSimplex::unit*(-iyAu1))*eps[1] +
		(taylorSimplex::x3+taylorSimplex::unit*(-iyAu2))*eps[2] +
		(taylorSimplex::x4+taylorSimplex::unit*(-iyAu3))*eps[3];
	taylorFunction A1 = *IA[0]+T*interval("-1");
	taylorFunction B1 = *IB[0]+T;
	A1.setReducibleState(0);
	B1.setReducibleState(0);
	const taylorFunction* IA1[1]= {&A1};
	const taylorFunction* IB1[1]= {&B1};
	double xA0[6],xB0[6],zA0[6],zB0[6];
	for (j=0;j<6;j++)
		{
		xA0[j]=xA[j]; xB0[j]=xB[j]; zA0[j]=zA[j]; zB0[j]=zB[j]; 
		}
	cellOption option; //int external_errorchecking=1;
	option.setPrintMode(cellOption::silent);
	if ((prove::recursiveVerifier
		(depth,domain(xA),domain(zA),domain(xA0),domain(zA0),IA1,1,option))&&
	    (prove::recursiveVerifier
		(depth,domain(xB),domain(zB),domain(xB0),domain(zB0),IB1,1,option))
	   ) return 1;
	return 0;
	}


void prove::recursiveVerifierQ(int depth,
	const domain& xAd,const domain& xBd,     /// current lower bound
	const domain& zAd,const domain& zBd,   // current upper bound
	const taylorFunction* IA[],const taylorFunction* IB[],
	int Nineq,cellOption& sym)
	// function should not change any of these parameters.
	// exception iteration counter in sym.
	{
	double xA[6],xB[6],zA[6],zB[6]; 
	int i;
	for (i=0;i<6;i++)
		{
		xA[i]=xAd.getValue(i); xB[i]=xBd.getValue(i);
		zA[i]=zAd.getValue(i); zB[i]=zBd.getValue(i);
		}
	// symtype 0 none, 1=split, 2=asym,
	if (!fitstogether(xA,xB)) 
		{ error::message("Rx-mismatch:"); printit(xA); printit(xB); }
	if (!fitstogether(zA,zB)) 
		{ error::message("Rz-mismatch:"); printit(zA); printit(zB); }
	stats(); 
	sym.augmentIterationCount();
	if ((sym.getIterationLimit()>0)&&
		(sym.getIterationLimit()<sym.getIterationCount()))
		{
		report_failure(xA,zA,"A:iteration limit exceeded");
		report_failure(xB,zB,"B:iteration limit exceeded");
		cout << "iteration limit is set at " << sym.getIterationLimit() << endl;
		return ;
		}
	int MAXDEPTH = 20;
	if (sym.getRecursionDepth()>0) MAXDEPTH=sym.getRecursionDepth();
	if (depth++ > MAXDEPTH) 
		{
		report_failure(xA,zA,"A:recursion limit exceeded");
		report_failure(xB,zB,"B:recursion limit exceeded");
		cout << "recursion depth is currently at " << MAXDEPTH << endl;
		return;
		}
	double zzA[6],zzB[6];
	if ((reducible(IA,Nineq) )&&(reducible(IB,Nineq))&&
		(unreducedQ(xA,xB,zA,zB)))
		{
		// should be 0..18
		for (i=sym.getStartingIndex();i<18;i++) 
		if (setreductionQ(i,xA,xB,zA,zB,zzA,zzB))
			{
			if (sym.skip(i)) continue;
			cout << "R" << i << "." << flush;
			recursiveVerifierQ
				(depth,xA,xB,zzA,zzB,IA,IB,Nineq,sym);
			};
		return;
		}
	// make a backup. verifyCellQ changes the parameters.
	double xxA[6],xxB[6];
	for (i=0;i<6;i++) 
		{xxA[i]=xA[i];zzA[i]=zA[i];xxB[i]=xB[i];zzB[i]=zB[i];}
	if (Nineq>MAXcount) 
		{
		cout << "There are " << Nineq << " inequalities." << endl;
		error::message("Increase MAXcount and recompile");
		return;
		}
	const taylorFunction* IIA[MAXcount];
	const taylorFunction* IIB[MAXcount];
	for (i=0;i<Nineq;i++) { IIA[i]=IA[i];  IIB[i]=IB[i]; }
	int NNineq = Nineq;
	// set bound on smaller diagonal:
	// a bad condition was removed on 6/9/97 // if (zzA[3]>8) { etc.
	// stuff that worked with the condition, still works, but this
	// should improve other cases as well.
 
	double z3=zzA[3];
	if (edgeBound::shortDiagMax(xxA[0],xxB[0],zzA[1],zzA[2],xxA[3],z3,
		  zzA[4],zzB[4],zzA[5],zzB[5]))
		{
		if (z3<xxA[3]) return;//nothing in domain. We are done.
		if (z3<zzA[3]) { zzA[3]=zzB[3]=z3; } // restrict domain
		}
	
 
	// Here is the main line of the procedure.  Check if it verifies.
	if (verifyCellQ(xxA,xxB,zzA,zzB,IIA,IIB,NNineq,sym)) return;
		//xxA,.. affected.
 
	// now start the recursion;
	if (NNineq<1) error::message("Empty recursion");
	if (breaksapart(depth,xA,xB,zzA,zzB,IIA,IIB,NNineq)) return;
	
	interMath::up();
	double yyA[6]; for (i=0;i<6;i++) yyA[i]= (xxA[i]+zzA[i])/2.0;//~center.
	double xAr[6],zAr[6];
	double yyB[6]; for (i=0;i<6;i++) yyB[i]= (xxB[i]+zzB[i])/2.0;//~center.
	for (i=1;i<4;i++) yyB[i]=yyA[i];
	double xBr[6],zBr[6];
	static const double epsilon_width = 1.0e-8;
	for (i=0;i<6;i++) { xAr[i]=xxA[i]; zAr[i]=zzA[i]; }
	for (i=0;i<6;i++) { xBr[i]=xxB[i]; zBr[i]=zzB[i]; }
	int imaxA[6],imaxB[6],iterA[6],iterB[6];
	for (i=0;i<6;i++) { imaxA[i]= ( zzA[i]>xxA[i]+epsilon_width? 2 : 1 ); }
	for (i=0;i<6;i++) { imaxB[i]= ( zzB[i]>xxB[i]+epsilon_width? 2 : 1 ); }
	double w0=zzA[0]-xxA[0]; 
	for (i=1;i<6;i++) 
		if (w0<zzA[i]-xxA[i]) w0=zzA[i]-xxA[i]; 
	for (i=0;i<6;i++) 
		if (w0<zzB[i]-xxB[i]) w0=zzB[i]-xxB[i]; 
	w0 = w0/2.0; //  approximate width;
	for (i=0;i<6;i++) if ((imaxA[i]>1)&&(zzA[i]-xxA[i]<w0)) imaxA[i]=1;
	for (i=0;i<6;i++) if ((imaxB[i]>1)&&(zzB[i]-xxB[i]<w0)) imaxB[i]=1;
	for (iterA[0]=0;iterA[0]<imaxA[0];iterA[0]++)  // at most 2^9 cases
	for (iterA[1]=0;iterA[1]<imaxA[1];iterA[1]++)
	for (iterA[2]=0;iterA[2]<imaxA[2];iterA[2]++)
	for (iterA[3]=0;iterA[3]<imaxA[3];iterA[3]++)
	for (iterA[4]=0;iterA[4]<imaxA[4];iterA[4]++)
	for (iterA[5]=0;iterA[5]<imaxA[5];iterA[5]++)
	for (iterB[0]=0;iterB[0]<imaxB[0];iterB[0]++)
	for (iterB[4]=0;iterB[4]<imaxB[4];iterB[4]++)
	for (iterB[5]=0;iterB[5]<imaxB[5];iterB[5]++)
		{
		iterB[1]=iterA[1]; iterB[2]=iterA[2]; iterB[3]=iterA[3];
		for (i=0;i<6;i++) 
		  {
		  xAr[i] = ( iterA[i] ? yyA[i] : xxA[i] );
		  zAr[i] = ( imaxA[i]-iterA[i]-1? yyA[i] : zzA[i] );
		  xBr[i] = ( iterB[i] ? yyB[i] : xxB[i] );
		  zBr[i] = ( imaxB[i]-iterB[i]-1? yyB[i] : zzB[i] );
		  }
		recursiveVerifierQ
			(depth,xAr,xBr,zAr,zBr,IIA,IIB,NNineq,sym);
		}
	}


int prove::generic(const domain& x,const domain& z,const taylorFunction& F)
    {
	domain x0 = x,z0 = z;
	const taylorFunction* I[1] = {&F};
	cellOption opt;
    return recursiveVerifier(0,x,z,x0,z0,I,1,opt);
    }


