//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


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
#include "recurse.h"

static inline double dabs(interval x)
	{
	return sup(max(x,-x));	
	}

static int fitstogether(const double x[6],const double y[6])
	{
	return ((x[1]==y[1])&&(x[2]==y[2])&&(x[3]==y[3]));
	}

static double upperboundQ(series cA,series cB,const double wA[6],
	const double wB[6],double eA,double eB)
	{
	up();
	double t = sup(cA.f) + sup(cB.f) + eA+eB;
	int k[3]={0,4,5},i;
	for (i=0;i<3;i++) t = t+ wA[k[i]]*dabs(cA.Df[k[i]]);
	for (i=0;i<3;i++) t = t+ wB[k[i]]*dabs(cB.Df[k[i]]);
	for (i=1;i<4;i++) t = t+ wB[i]*dabs(cB.Df[i]+cA.Df[i]);
	return t;
	}

static double lowerboundQ(series cA,series cB,const double wA[6],
	const double wB[6],double eA,double eB)
	{
	down();
	double t = inf(cA.f) + inf(cB.f) - eA-eB;
	int k[3]={0,4,5},i;
	for (i=0;i<3;i++) t = t+ (-wA[k[i]])*dabs(cA.Df[k[i]]);
	for (i=0;i<3;i++) t = t+ (-wB[k[i]])*dabs(cB.Df[k[i]]);
	for (i=1;i<4;i++) t = t+ (-wB[i])*dabs(cB.Df[i]+cA.Df[i]);
	return t;
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
		default : error_msg("setreductionQ out of range");
		}
	return 1;
	}

static inline int sgn(interval x) 
	{ if (inf(x)>0.0) return 1;
			else if (sup(x)<0.0) return -1; else return 0;
	}

static int same_sgnQ(const interval xA[6],const interval xB[6],
	const interval yA[6],const interval yB[6])
	{
	int k[3]={0,4,5},i;
	for (i=0;i<3;i++) if (sgn(xA[k[i]])!=sgn(yA[k[i]])) return 0;
	for (i=0;i<3;i++) if (sgn(xB[k[i]])!=sgn(yB[k[i]])) return 0;
	for (i=1;i<4;i++) if (sgn(xA[i]+xB[i])!=sgn(yA[i]+yB[i])) return 0;
	return 1;
	}

static void delete_ineqQ(series cA[],series cB[],double eA[],double eB[],
	ineq IA[],ineq IB[],int& Nineq,int i)
	{
	Nineq--; if (Nineq<0) error_msg("unexpected negative numberQ");
	int j;
	for (j=i;j<Nineq;j++)
		{ cA[j]=cA[j+1]; eA[j]=eA[j+1]; IA[j]=IA[j+1]; 
		  cB[j]=cB[j+1]; eB[j]=eB[j+1]; IB[j]=IB[j+1]; }
	}

static double deltainf(double x1,double x2,double x3,double x4,double x5,
        double x6)
        {
        down();
        return
         ((-x2)*x3)*x4 +((- x1)*x3)*x5 +((- x1)*x2)*x6 +((- x4)*x5)*x6 +
   x3*(x1 + x2 + x4 + x5)*x6 +  (x3*(-x3-x6))*x6 +
   x2*x5*(x1 + x3 + x4 + x6) + x2*(x5*(-x2-x5)) +
        x1*x4*(x2 + x3 + x5 + x6)+ x1*(x4*(-x1-x4));
        }

/* global option */
static int restrictW=0;
static double WVALUE = 0.0;
void setWCUTOFF(double x)
	{
	restrictW = 1;
	WVALUE=x;
	}

int verify_cellQ(double xA[6],double xB[6],double zA[6],double zB[6],
		ineq IA[],ineq IB[],int& Nineq)
	// return true if all verifies or if all counterexamples have been
	// 	properly reported.
	//return false if x,z ... require further investigation.
	{
	if (!fitstogether(xA,xB))
		{
		error_msg("Qx-mismatch"); printit(xA); printit(xB); return 0;
		}
	if (!fitstogether(zA,zB))
		{
		error_msg("Qz-mismatch"); printit(zA); printit(zB); return 0;
		}
	// get out if delta is possibly negative.
	if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<=0.0) return 0;
	if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.0) return 0;
	static const int MAXineq=20;
	double yA[6],yB[6],wA[6],wB[6]; 
	series cA[MAXineq],cB[MAXineq]; double eA[MAXineq],eB[MAXineq];
	if (Nineq>MAXineq) 
		{
		error_msg("array overflow in verify_cell");
		return 0;
		}
	int i,j;
	centerform(xA,zA,yA,wA); 
	centerform(xB,zB,yB,wB); 
	// get out fast if any of the crude taylor bounds hold.
	for (i=0;i<Nineq;i++)
		{
		cA[i]=IA[i].s(yA);
		cB[i]=IB[i].s(yB);
		if (!(IA[i].set_taylor_error(xA,zA,wA,eA[i]))) return 0;
		if (!(IB[i].set_taylor_error(xB,zB,wB,eB[i]))) return 0;
		if ((!finite(eA[i])) || (!finite(eB[i])) )
			{
			error_msg("infinite taylor bound");
			return 0; 
			}
		if (upperboundQ(cA[i],cB[i],wA,wB,eA[i],eB[i])< 0.0) return 1;
		}
	static const double epsilon_width = 1.0e-8;
	if (max(max(wA),max(wB)) < epsilon_width) 
		{
		report_failure(xA,zA,"A:isolated point");
		report_failure(xB,zB,"B:isolated point");
		cout.precision(20);
		for (i=0;i<Nineq;i++)
			{
			down();
			cout << "  value=[A:" << lowerbound(cA[i],wA,eA[i]) << flush;
			up();
			cout << "," << upperbound(cA[i],wA,eA[i]) << "]" << flush;
			down();
			cout << "  [B:" << lowerbound(cB[i],wB,eB[i]) << flush;
			up();
			cout << "," << upperbound(cB[i],wB,eB[i]) << "]\n" << flush;
			}
		cout << flush;
		return 1;
		}
	i=0; while (i<Nineq)
		{
		if (lowerboundQ(cA[i],cB[i],wA,wB,eA[i],eB[i]) > 0.0)
			{
			delete_ineqQ(cA,cB,eA,eB,IA,IB,Nineq,i); 
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
	if (restrictW) WCUTOFF=WVALUE; // patch 6/26/97
	int s;
	if ((max(max(wA),max(wB))<WCUTOFF)&&(Nineq>1))
	{
	double yAn[6],yAu[6],yBn[6],yBu[6];
		// look at the lowest & highest corners
	int k[3]={0,4,5};
	series cAn,cAu,cBn,cBu;
	int mixedsign;
	double margin =0.0;
	for (i=0;i<Nineq;i++) if (sup(cA[i].f+cB[i].f)< 0.0)
		{
		mixedsign=0;
		for (j=0;j<3;j++)
			{
			s = sgn(cA[i].Df[k[j]]);
			yAn[k[j]]= (s>0 ? xA[k[j]]: zA[k[j]]);
			yAu[k[j]]= (s>0 ? zA[k[j]]: xA[k[j]]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		for (j=0;j<3;j++)
			{
			s = sgn(cB[i].Df[k[j]]);
			yBn[k[j]]= (s>0 ? xB[k[j]]: zB[k[j]]);
			yBu[k[j]]= (s>0 ? zB[k[j]]: xB[k[j]]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		for (j=1;j<4;j++)
			{
			s = sgn(cB[i].Df[j]+cA[i].Df[j]);
			yAn[j]=yBn[j]= (s>0 ? xB[j]: zB[j]);
			yAu[j]=yBu[j]= (s>0 ? zB[j]: xB[j]);
			if (s==0) mixedsign= 1;
			}
		if (mixedsign) { mixedsign=0; continue; }
		cAn = IA[i].s(yAn); cAu= IA[i].s(yAu);
		cBn = IB[i].s(yBn); cBu= IB[i].s(yBu);
		if ((inf(min(-cAn.f-cBn.f,-cAu.f-cBu.f))>margin)
			&&(same_sgnQ(cA[i].Df,cB[i].Df,cAn.Df,cBn.Df))
			&&(same_sgnQ(cA[i].Df,cB[i].Df,cAu.Df,cBu.Df)))
			{
			margin = inf(min(-cAn.f-cBn.f,-cAu.f-cBu.f));
			move_first(cA,eA,IA,i);
			move_first(cB,eB,IB,i);
			}
		}
	if (margin>0.0) Nineq =1; // Disregard the rest of the inequalities;
	} // if max(w) 
	return 0;
	} // end verify_cellQ.


static int breaksapart(int depth,const double xA[6],
	const double xB[6],const double zA[6],
	const double zB[6],const ineq IA[],const ineq IB[],int Nineq)
	{
	if (Nineq<1) error_msg("Lacking in inequalities");
	if (Nineq>1) return 0;
	if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<=0.0) return 0;
	if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.0) return 0;
	double yA[6],yB[6],wA[6],wB[6],yAn[6],yBn[6],yAu[6],yBu[6];
	series cA,cB,cAu,cBu,cAn,cBn;
	centerform(xA,zA,yA,wA);
	centerform(xB,zB,yB,wB);
	cA=IA[0].s(yA);
	cB=IB[0].s(yB);
	double WCUTOFF=0.3;
	if (max(zA[0],zB[0])>6.00) WCUTOFF=0.1; // things are unstable here!
	if (max(max(wA),max(wB)) >WCUTOFF) return 0;
	int j,u,sgnA[6],sgnB[6],k[6]={1,2,3,0,4,5};
	for (j=0;j<6;j++)
		{
		u = k[j];
		sgnA[u] = sgn(cA.Df[u] + (j<3 ? cB.Df[u] : zero ) );
		if (sgnA[u]==0) return 0;
		yAn[u]= (sgnA[u]>0 ? xA[u] : zA[u]);
		yAu[u]= (sgnA[u]>0 ? zA[u] : xA[u]);
		sgnB[u] = sgn(cB.Df[u] + (j<3 ? cA.Df[u] : zero ) );
		if (sgnB[u]==0) return 0;
		yBn[u]= (sgnB[u]>0 ? xB[u] : zB[u]);
		yBu[u]= (sgnB[u]>0 ? zB[u] : xB[u]);
		}
	cAn=IA[0].s(yAn); cAu=IA[0].s(yAu);
	cBn=IB[0].s(yBn); cBu=IB[0].s(yBu);
	if (!(same_sgnQ(cA.Df,cB.Df,cAn.Df,cBn.Df))) return 0;
	if (!(same_sgnQ(cA.Df,cB.Df,cAu.Df,cBu.Df))) return 0;
	interval e,eps[6];
	e = (cAu.f - cBu.f)/two;
	for (j=0;j<6;j++) eps[j]= (cAu.Df[j]-cBu.Df[j])/two;
	// test these values;
	if ((sup(cAu.f)> inf(e)) ||(sup(cAn.f)> inf(e)) 
	   ||(sup(cBu.f)> inf(-e)) ||(sup(cBn.f)> inf(-e)) ) return 0;
	combo A1,B1,T;
	interval iyAu1(yAu[1],yAu[1]),iyAu2(yAu[2],yAu[2]),iyAu3(yAu[3],yAu[3]);
	// T is the linear bound on A at yAu:
	T = simplex::unit*e +
		(simplex::x2-simplex::unit*iyAu1)*eps[1] +
		(simplex::x3-simplex::unit*iyAu2)*eps[2] +
		(simplex::x4-simplex::unit*iyAu3)*eps[3];
	A1 = *((combo*) IA[0].details); // grab details.
	B1 = *((combo*) IB[0].details);
	A1 = A1-T;
	B1 = B1+T;
	ineq IA1[1]={ineq(&sec_combo,&combo_fn,0)},
	     IB1[1]={ineq(&sec_combo,&combo_fn,0)};
	IA1[0].setdetails((int*) &A1);
	IB1[0].setdetails((int*) &B1);
	double xA0[6],xB0[6],zA0[6],zB0[6];
	for (j=0;j<6;j++)
		{
		xA0[j]=xA[j]; xB0[j]=xB[j]; zA0[j]=zA[j]; zB0[j]=zB[j]; 
		}
	int external_errorchecking=1;
	if ((recursive_verifier
		(depth,xA,zA,xA0,zA0,IA1,1,external_errorchecking))&&
	    (recursive_verifier
		(depth,xB,zB,xB0,zB0,IB1,1,external_errorchecking))
	   ) return 1;
	return 0;
	}

static const int Nskip=30;
static int skip_these[Nskip];
static int skipped=0;

void skipcases(const int skiplist[],int len)
	{
	int i;
	if (len>Nskip) { error_msg("skip array out of bounds"); len=Nskip; }
	for (i=0;i<len;i++) skip_these[i]=skiplist[i];
	skipped=len;
	cout << "\nWarning: skipping R-cases ";
	for (i=0;i<len;i++) cout << skiplist[i] << " ";
	cout << endl << flush;
	}

static int skip(int i)
	{
	for (int j=0;j<skipped;j++)  if (i==skip_these[j]) return 1;
	return 0;
	}

void recursive_verifierQproto(int depth,
		const double xA[6],const double xB[6],     /// current cell
		const double zA[6],const double zB[6],   // boundary
		const ineq IA[],const ineq IB[],int Nineq,int sym)
	// function should not change any of these parameters.
	{
	// symtype 0 none, 1=split, 2=asym,
	if (!fitstogether(xA,xB)) 
		{ error_msg("Rx-mismatch:"); printit(xA); printit(xB); }
	if (!fitstogether(zA,zB)) 
		{ error_msg("Rz-mismatch:"); printit(zA); printit(zB); }
	stats(); 
	int i;
	static const int MAXDEPTH = 20;
	if (depth++ > MAXDEPTH) 
		{
		report_failure(xA,zA,"A:recursion limit exceeded");
		report_failure(xB,zB,"B:recursion limit exceeded");
		return;
		}
	double zzA[6],zzB[6];
	if ((reducible(IA,Nineq) )&&(reducible(IB,Nineq))&&
		(unreducedQ(xA,xB,zA,zB)))
		{
		// should be 0..18
		for (i=sym;i<18;i++) if (setreductionQ(i,xA,xB,zA,zB,zzA,zzB))
			{
			if (skip(i)) continue;
			cout << "R" << i << "." << flush;
			recursive_verifierQproto
				(depth,xA,xB,zzA,zzB,IA,IB,Nineq,sym);
			};
		return;
		}
	// make a backup. verify_cellQ changes the parameters.
	double xxA[6],xxB[6];
	for (i=0;i<6;i++) 
		{xxA[i]=xA[i];zzA[i]=zA[i];xxB[i]=xB[i];zzB[i]=zB[i];}
	static const int MAXineq=20;
	if (Nineq>MAXineq) 
		{
		error_msg("inequality quota exceeded");
		return;
		}
	ineq IIA[MAXineq],IIB[MAXineq];
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
	if (verify_cellQ(xxA,xxB,zzA,zzB,IIA,IIB,NNineq)) return;
		//xxA,.. affected.

	// now start the recursion;
	if (NNineq<1) error_msg("Empty recursion");
	if (breaksapart(depth,xA,xB,zzA,zzB,IIA,IIB,NNineq)) return;
	
	nearest();
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
		recursive_verifierQproto
			(depth,xAr,xBr,zAr,zBr,IIA,IIB,NNineq,sym);
		}
	}

// version where case R0 is skipped by symmetry. // obsolte fn.
void recursive_verifierQsym(int depth,
		const double xA[6],const double xB[6],     /// current cell
		const double zA[6],const double zB[6],   // boundary
		const ineq IA[],ineq IB[],int Nineq)
	{
	recursive_verifierQproto(depth,xA,xB,zA,zB,IA,IB,Nineq,1);
	}

// nothing skipped here
void recursive_verifierQ(int depth,
		const double xA[6],const double xB[6],     /// current cell
		const double zA[6],const double zB[6],   // boundary
		const ineq IA[],const ineq IB[],int Nineq)
	{
	recursive_verifierQproto(depth,xA,xB,zA,zB,IA,IB,Nineq,0);
	}


