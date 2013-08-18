#include <iomanip.h>
#include <stdlib.h>
#include "numerical.h"
#include "constants.h"
#include "morefn.h"
#include "quoinfn.h"
#include <math.h>

class iter {
    double* xmin;
	double* xmax;
	double* x;
    int numiter,numargs,nconstr;
    void (*func)(int numargs,int whichFn,double* x,double* ret,void*);
    void (*constraintfunc)
        (int numargs,int which,double* x,double* ret,void*);
    iter(int);
    ~iter();
    };

iter::~iter() 
	{ delete[] xmin; 
	  delete[] xmax; 
		delete[] x; }

static double vorAnchor3(double y1,double y2,double y6) // was 2
    {
	double x = y2+y6;
     return (0.0002  
	-0.2695279326151798 + 0.1833230667013778*y1 - 0.02783887375001181*y1*y1
	-0.0152253
	+0.7557773828234548 - 0.3239044460786886*x + 0.0346916048615081*x*x);
	//(- 0.027*(y2-2.)-0.0264*(y6-2.));
    }

static double vorAnchor2(double y1,double y2,double y6) 
    {
	double x = y2+y6;
     return (0.00011
	-0.2695279326151798 + 0.1833230667013778*y1 - 0.02783887375001181*y1*y1
	-0.0152253
	+0.4384851103526791 - 0.167484482694134*x + 0.01541738104479281*x*x);
    }

static void nofunc(int numargs,int whichFn,double* x,double* ret,void*)
    {
    cout << "nofunc should not be called" << endl << flush;
    }

double dips(double x[16])
    {
    return
        dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
            +dihedraly(x[0],x[2],x[7],x[6],x[3],x[4])
            +dihedraly(x[0],x[7],x[11],x[9],x[10],x[8])
            +dihedraly(x[0],x[11],x[13],x[12],x[14],x[10])
            +dihedraly(x[0],x[13],x[1],x[15],x[5],x[14])
            -2.0*global::pi;
    }

double gammaAX(double y1,double y2,double y3,double y4,double y5,double y6)
	{
	return gamma(y1,y2,y3,y4,y5,y6)+0.419351*solid(y1,y2,y3,y4,y5,y6);
	}


int INEQ_NUMBER=0;
static void generic(int numargs,int whichFn,double* x, double* ret,void*)
	{
	switch (INEQ_NUMBER) {


	case 348940660+1:
	*ret= 2.06*global::pt
		-(
		gamma(x[0],x[1],x[2],x[3],x[4],x[5])
		+gamma(x[0],x[2],x[7],x[6],x[3],x[4])
		+gamma(x[0],x[7],x[11],x[9],x[10],x[8])
		+gamma(x[0],x[11],x[13],x[12],x[14],x[10])
		+(vor_analytic(x[0],x[13],x[1],x[15],x[5],x[14]))
		);
		break;
	case 2:
	*ret = -x[3]; break;

		case 91:
            *ret=-gamma(x[0],x[1],x[2],x[3],x[4],x[5])
                -0.12*(x[0]-2.)-0.081*(x[1]+x[2]-4.)
				+0.029*(x[3]-2.51)
                -0.113*(x[4]+x[5]-4.); break;
        case 92:
            *ret=-vorVc(x[0],x[1],x[2],x[3],x[4],x[5])
                -0.12*(x[0]-2.)-0.081*(x[1]+x[2]-4.)
				+0.029*(x[3]-2.51)
                -0.113*(x[4]+x[5]-4.); break;
        case 93:
            *ret=-vorVc(x[0],x[1],x[2],x[3],x[4],x[5]) +0.014
                -0.12*(x[0]-2.)-0.081*(x[1]+x[2]-4.)
				+0.029*(x[3]-2.51)
                -0.113*(x[4]+x[5]-4.); 
				break;
        case 94: case 95:
            *ret=-vorVc(x[0],x[1],x[2],x[3],x[4],x[5])
                -0.12*(x[0]-2.)-0.081*(x[1]+x[2]-4.)
				+0.029*(x[3]-2.51)
                -0.113*(x[4]+x[5]-4.); break;
		case 96:
			*ret = dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
				-1.69
				+0.155*(x[4]-2.)
				+0.395*(x[5]-2.51)
				+0.58*(x[2]-2.) 
				+0.40*(x[1]-2.) 
				-0.214*(x[0]-2.); break;
		case 97:
			*ret = x[12]+x[3]+x[6]+x[9]+2.1*(x[0]-2.); break;
		case 98:
			*ret = (x[1]+x[5])+(x[2]+x[4])+(x[7]+x[8])+(x[10]+x[11])
					+(x[13]+x[14]); break;
		case 99:
			*ret = 
		-(
		gammaAX(x[0],x[1],x[2],x[3],x[4],x[5])
		+gammaAX(x[0],x[2],x[7],x[6],x[3],x[4])
		+gammaAX(x[0],x[7],x[11],x[9],x[10],x[8])
		+gammaAX(x[0],x[11],x[13],x[12],x[14],x[10])
		+gammaAX(x[0],x[13],x[1],x[15],x[5],x[14])
		);
		case 100:
			*ret = octavorVc(x[0],x[1],x[2],x[3],x[4],x[5])-
				gamma(x[0],x[1],x[2],x[3],x[4],x[5]);
			break;
		case 101: // old:
		case 102:
			*ret = dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
				- 0.49*(x[0]-2.51)
				+0.440*(x[1]+x[2]+x[4]+x[5]-8.)
				-0.82*(x[3]-2) - 1.392; 
			*ret = -dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
				+0.495*(x[0]-2.51)
				-0.214*(x[1]+x[2]+x[4]+x[5]-8.)
				+1.05*(x[3]-2.)+ 1.395;
			*ret = dihedraly(x[1],x[0],x[2],x[4],x[3],x[5])
				+0.38*(x[0]-2.51)-0.15*(x[1]-2.)+0.09*(x[2]-2.)
				+0.54*(x[3]-2.)-0.57*(x[4]-2.)+0.24*(x[5]-2.)-1.086;
			*ret = -dihedraly(x[1],x[0],x[2],x[4],x[3],x[5])
				-0.375*(x[0]-2.51) +0.33*(x[1]-2.)+ 0.11*(x[2]-2.)
				-0.36*(x[3]-2.) +0.72*(x[4]-2.)+0.034*(x[5]-2.)+1.0881;
			*ret = solid(x[0],x[1],x[2],x[3],x[4],x[5])
				+0.42*(x[0]-2.51)
				+0.165*(x[1]+x[2]-4.) - 0.06*(x[3]-2.)-0.135*(x[4]+x[5]-4.)
				- 0.4266;
			*ret = -solid(x[0],x[1],x[2],x[3],x[4],x[5])
				-0.265*(x[0]-2.51) - 0.06*(x[1]+x[2]-4.)
				+0.124*(x[3]-2.)+0.296*(x[4]+x[5]-4.)
				+0.42715;
		
			{
			double sig =
			(INEQ_NUMBER==102 ? vorNu(x[0],x[1],x[2],x[3],x[4],x[5]) :
				gammaNu(x[0],x[1],x[2],x[3],x[4],x[5]));	
			double dih1 = dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
			*ret = -sig 
				+0.112*(x[0]-2.51)
				-0.142*(x[1]+x[2]-4.) - 0.16*(x[3]-2.)
				-0.074*(x[4]+x[5]-4.) ;
			*ret = -sig
				//+4.10113*dih1 -4.3223;
				//+0.80449*dih1 -0.9871;
				//+0.70186* dih1 -0.8756;
				//+0.24573*dih1 -0.3404;
				//+0.00154* dih1 -0.0024;
				-0.07611*dih1+  0.11; // new constant.
			}

			/*
			*ret = -gammaNu(x[0],x[1],x[2],x[3],x[4],x[5]);

				{
				double dih1 = dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
				double ta = 
				(INEQ_NUMBER==102 ? tauVnu(x[0],x[1],x[2],x[3],x[4],x[5]):
					tauGnu(x[0],x[1],x[2],x[3],x[4],x[5]));
				// *ret = ta +4.16523*dih1 - 4.42873;
				// *ret = ta +0.78701*dih1 - 1.01104;
				// *ret = ta + 0.77627 *dih1-  0.99937;
				// *ret = ta + 0.21916 *dih1-  0.34877;
				// *ret = ta + 0.05107 *dih1-  0.11434;
				// *ret = ta  -0.07106* dih1+ 0.06429;
				}
			*/
				
		break;
	case 103:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])
			-0.145*(x[0]-2.) - 0.081*(x[1]+x[2]-4.)
			-0.133*(x[4]+x[5]-4.);
		break;
	case 104:
		*ret = x[0]+x[1]+x[2]; break;
	case 105:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5])
				-0.058*(x[0]-2.)-0.1*(x[1]+x[2]-4.)
			-0.165*(x[3]-2.)-0.12*(x[4]-2.51)-0.115*(x[5]-2.77)
			-0.0777;
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5])
				-0.058*(x[0]-2.)-0.05*(x[1]+x[2]-4.)
			-0.16*(x[3]-2.314)-0.13*(x[4]-2.51)-0.13*(x[5]-2.51)
			-0.09337;
		*ret = -vor_analytic(x[0],x[1],x[2],x[3],x[4],x[5])
				-0.058*(x[0]-2.)-0.08*(x[1]+x[2]-4.)
			-0.16*(x[3]-2.)-0.21*(x[4]+x[5]-2.0*2.51)
			-0.0571;
			break;
	case 106:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])
			-0.145*(x[0]-2.) - 0.081*(x[1]+x[2]-4.)
			-0.16*(x[4]+x[5]-4.)
			+0.001;
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])
			-0.03*(x[0]-2.) - 0.03*(x[1]+x[2]-4.)
			-0.16*(x[4]+x[5]-4.);
			
		break;
	case 107:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5]);
			break;
	case 108:
		*ret = vorAnchor2(x[0],x[1],x[2])-vorAnchor(x[0],x[1],x[2]);
			break;
	case 109:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])
			-0.03*(x[0]-2.) - 0.03*(x[1]+x[2]-4.)
			-0.16*(x[4]+x[5]-4.);
		break;
	case 110:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])
			-0.03*(x[0]-2.) - 0.03*(x[1]+x[2]-4.)
			-0.094*(x[4]+x[5]-4.3)
			-0.0481;
		break;
	case 111:
		*ret = -vor_analytic(x[0],x[1],x[2],x[3],x[4],x[5]); break;
	case 112:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5]); break;
	case 113: case 114:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5]); break;
	case 115:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5]); break;
	case 116:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5]); break;
	case 117:
		*ret = -vorVc(x[0],x[1],x[2],x[3],x[4],x[5])-
			vorVc(x[6],x[1],x[2],x[3],x[7],x[8]); break;
	case 118:
		*ret=dihedraly(x[1],x[2],x[0],x[4],x[5],x[3])-
                beta(arc(x[0],1.255,1.6),x[0],x[1],x[5]); break;
	case 119:
		*ret=dihedraly(x[1],x[2],x[0],x[4],x[5],x[3])-
                beta(arc(x[0],1.255,1.6),x[0],x[1],x[5]); break;

	case 355:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + dih2*(0.198867);
		*ret= -(
		Fsig+ 0.051272725+y1*(-0.171087) +y2*(0.282483) +y3*(0.0423759)
			+y5*(-0.0269357) +y6*(-0.0813089) +(dih1-pi/2)*(0.0761186));
		break;
		}

	case 617:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = gamma(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ 1999.652492+y1*(654.2324352) +y2*(322.54) +y3*(0.449699) +
y5*(0.444429) +y6*(-2000) +(dih1-pi/2)*(0.356683);

		*ret= -(F); break;
		break;
		}
		

	case 688:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + (dih2+dih3)*(0.198867);
double F = Fsig+ 7.56484+y1*(-2.78327) +y2*(0.225892) +y3*(-0.147887) +
		y5*(-0.206484) +y6*(0.187246) +(dih1-pi/2)*(0.0767791);
		*ret= -(F); break;
		break;
		}

	case 690:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + dih2*(0.198867);
double F = Fsig+ 7.58471+y1*(-2.9616) +y2*(0.0112946) +y3*(0.311179) +y5*(0.181643) +y6
*(-0.112645) +(dih1-pi/2)*(0.171553);
		*ret= -(F); break;
		break;
		}

	case 703:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + dih3*(0.198867);
double F = Fsig+ 2000+y1*(-623.13575) +y2*(-29.7859) +y3*(0.373676) +y5*(0.394828) +y6* (-89.7991) +(dih1-pi/2)*(0.296739);

		*ret= -(F); break;
		break;
		}

	case 705:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ -2000+y1*(2000) +y2*(304.735) +y3*(-0.171058) +y5*(-0.186587) +y6*(-2000) +(dih1-pi/2)*(0.296739);

		*ret= -(F); break;
		break;
		}

	case 707:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ -2000+y1*(2000) +y2*(304.727) +y3*(-0.183459) +y5*(-0.167931) +y6*(-2000) +(dih1-pi/2)*(0.296739);

		*ret= -(F); break;
		break;
		}

	case 709:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ -2000.21+y1*(527.638) +y2*(122.604) +y3*(-0.228975) +y5*(-0.163413) +y6*(122.596) +(dih1-pi/2)*(0.296739);

		*ret= -(F); break;
		break;
		}

	case 761:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + (dih2+dih3)*(0.198867);
double F = Fsig+ 17.2803+y1*(-6.138444713) +y2*(0.18441) +y3*(-0.165877) +y5*(-0.211226) +y6*(0.138639) +(dih1-pi/2)*(0.0767791);

		*ret= -(F); break;
		break;
		}

	case 765:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + (dih2+dih3)*(0.198867);
double F = Fsig+ 19.6258005+y1*(-6.92706975) +y2*(0.190012) +y3*(-0.193187) +y5*(-0.250315) +y6*(0.138883) +(dih1-pi/2)*(0.0837391);
		*ret= -(F); break;
		break;
		}

	case 837:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
		double Fsig = sig + (-0.1906) + (dih2+dih3)*(0.198867);
double F = Fsig+ 7.61404+y1*(-2.80038) +y2*(0.226457) +y3*(-0.147744) +y5*(-0.208188) + y6*(0.187877) +(dih1-pi/2)*(0.0784741);

		*ret= -(F); break;
		break;
		}

	case 859:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + dih3*(0.198867);
double F = Fsig+ -15.1014+y1*(4.23632) +y2*(0.0999799) +y3*(0.70026) +y5*(0.749277) +y6
*(-0.00331063) +(dih1-pi/2)*(0.17892);

		*ret= -(F); break;
		break;
		}

	case 882:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + dih2*(0.198867);
double F = Fsig+ 22.90391+y1*(-8.1997) +y2*(-0.165254) +y3*(0.261357) +y5*(0.168103) +y6*(-0.120041) +(dih1-pi/2)*(0.170067);

		*ret= -(F); break;
		break;
		}

	case 899:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + dih2*(0.198867);
double F = Fsig+ -30.293+y1*(9.796300225) +y2*(0.192514) +y3*(0.471269) +y5*(0.376129) +y6*(0.24802) +(dih1-pi/2)*(0.171553);

		*ret= -(F); break;
		break;
		}

	case 969:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
	double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ -15.9098+y1*(4.75617) +y2*(0.741197) +y3*(-0.118936) +y5*(-0.0420991) +y6*(0.736019) +(dih1-pi/2)*(0.0784741);

		*ret= -(F); break;
		break;
		}

	case 972:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
	double Fsig = sig + (-0.1906) + dih2*(0.198867);
double F = Fsig+ 0.369222+y1*(-0.661767) +y2*(-0.121749) +y3*(0.534629) +y5*(0.427205)
+y6*(-0.0958335) +(dih1-pi/2)*(0.174342);

		*ret= -(F); break;
		break;
		}

	case 1000:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + 0*(0.198867);
double F = Fsig+ 0.840013+y1*(-0.372774) +y2*(0.0475567) +y3*(0.332565) +y5*(-0.186431)
 +y6*(0.00859412) +(dih1-pi/2)*(0.0761186);

		*ret= -(F); break;
		break;
		}

	case 1008:
		{
		double y1 = x[0], y2=x[1], y3=x[2], y4=x[3], y5=x[4], y6=x[5];
		double dih1=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5]);
		double dih2=dihedraly(x[1],x[0],x[2],x[4],x[3],x[5]);
		double dih3=dihedraly(x[2],x[0],x[1],x[5],x[3],x[4]);
		double pi = global::pi;
		double sig = octavor(x[0],x[1],x[2],x[3],x[4],x[5]);
double Fsig = sig + (-0.1906) + (dih2+dih3)*(0.198867);
double F = Fsig+ 4.721555+y1*(-1.71994) +y2*(0.0332922) +y3*(0.084638) +y5*(0.0501668)
+y6*(-0.191494) +(dih1-pi/2)*(0.0784741);

		*ret= -(F); break;
		break;
		}



	//Z-ineq
		// start of first page of inequalities for Section 2, SPIV.
		default : cout << "generic default "<< INEQ_NUMBER << endl << flush;
			*ret=0;
		}
	}


static void ConstraintPage1(int numargs,int whichFn,double* x,double* ret,void*)
    {
	*ret = 0;
	switch (INEQ_NUMBER) {

    case 348940660+1 :
        switch(whichFn) {
        case 1 : *ret=dips(x); break;
        case 3 : *ret= -(radf(x[1],x[13],x[15])-global::sqrt2); break;
        case 2 : *ret=-(radf(x[5],x[14],x[15])-global::sqrt2); break;
        }
        break;
	case 2 :
		switch(whichFn) {
		case 1 : *ret=dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])-1.771;
		break;
		case 2 : *ret=x[4]+x[5]+x[1]+x[2]-9.319; break;
		}
		break;
	case 91: 
            switch(whichFn) {
            case 1: *ret=radf(x[3],x[4],x[5])-global::sqrt2; break;
            case 2: *ret=radf(x[1],x[2],x[3])-global::sqrt2; break;
            }
            break;
	case 94: 
            *ret=global::sqrt2-radf(x[3],x[4],x[5]); break;
	case 95: 
            *ret=global::sqrt2-radf(x[3],x[2],x[1]); break;
	case 97:
			*ret=global::pi*2.-dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
			-dihedraly(x[0],x[2],x[7],x[6],x[8],x[4])
			-dihedraly(x[0],x[7],x[11],x[9],x[10],x[8])
			-dihedraly(x[0],x[11],x[1],x[12],x[5],x[10]);
			break;
	case 98:
			*ret=-global::pi*2.
			+dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
			+dihedraly(x[0],x[2],x[7],x[6],x[8],x[4])
			+dihedraly(x[0],x[7],x[11],x[9],x[10],x[8])
			+dihedraly(x[0],x[11],x[13],x[12],x[14],x[10])
			+dihedraly(x[0],x[13],x[1],x[15],x[5],x[14]);
			break;
	case 99:
		switch(whichFn)
			{
			case 1:
			*ret=-global::pi*2.
			+dihedraly(x[0],x[1],x[2],x[3],x[4],x[5])
			+dihedraly(x[0],x[2],x[7],x[6],x[8],x[4])
			+dihedraly(x[0],x[7],x[11],x[9],x[10],x[8])
			+dihedraly(x[0],x[11],x[13],x[12],x[14],x[10])
			+dihedraly(x[0],x[13],x[1],x[15],x[5],x[14]);
			break;
		case 2:
			*ret=-global::sqrt2+radf(x[13],x[1],x[15]); break;
		case 3:
			*ret=-global::sqrt2+radf(x[15],x[5],x[14]); break;
		case 4:
			-1.41+rady(x[0],x[1],x[2],x[3],x[4],x[5]); break;
		case 5:
			-1.41+rady(x[0],x[2],x[7],x[6],x[8],x[4]); break;
		case 6:
			-1.41+rady(x[0],x[7],x[11],x[9],x[10],x[8]); break;
		case 7:
			-1.41+rady(x[0],x[11],x[13],x[12],x[14],x[10]); break;
		}
		break;
	case 102:
		*ret= global::sqrt2-radf(x[0],x[1],x[5]); break;
	case 103:
		switch(whichFn)
		{
		case 1: *ret=-global::sqrt2+radf(x[1],x[2],x[3]); break;
		case 2: *ret=-global::sqrt2+radf(x[3],x[4],x[5]); break;
		}
		break;
	case 104:
		*ret = +global::sqrt2-radf(x[0],x[1],x[2]); break;
	case 105: case 107:
		*ret = global::sqrt2-radf(x[3],x[4],x[5]); break;
	case 106:
		*ret = -gamma(x[0],x[1],x[2],x[3],x[4],x[5])-0.0514; break;
	case 109:
		*ret = -4.3+x[4]+x[5]; break;
	case 110:
		switch(whichFn)
		{
		case 1 : *ret = 4.3-x[4]-x[5]; break;
		case 2 : *ret = -global::sqrt2+radf(x[3],x[4],x[5]); break;
		}
		break;
	case 117:
		switch(whichFn)
		{
		case 1 : *ret=crossdiag(x)-3.2; break;
		case 2 : *ret=-crossdiag(x)+global::sqrt8; break;
		}
		break;
	case 108:
		*ret = x[1]+x[2]-2.*2.29; break;

	// f(126,135)=0 0;
	case 617:  
		switch(whichFn) {
		case 2: *ret = radf(x[0],x[1],x[5])-global::sqrt2; break;
		case 1: *ret = radf(x[0],x[2],x[4])-global::sqrt2; break;
		}
		break;

	// f(126,135)=0 1;
	case 355: case 688: case 705 : case 707 : case 709 :
	case 761: case 765: case 837 : case 969: 
		switch(whichFn) {
		case 2: *ret = radf(x[0],x[1],x[5])-global::sqrt2; break;
		case 1: *ret = -radf(x[0],x[2],x[4])+global::sqrt2; break;
		}
		break;

	// f(126,135)=1 0;
	case 690 : case 703 : case 859 : case 882: case 899:
	case 972 : case 1000:
		switch(whichFn) {
		case 2: *ret = -radf(x[0],x[1],x[5])+global::sqrt2; break;
		case 1: *ret = +radf(x[0],x[2],x[4])-global::sqrt2; break;
		}
		break;

	// f(126,135)=1 1;
	case 1008:
		switch(whichFn) {
		case 2: *ret = -radf(x[0],x[1],x[5])+global::sqrt2; break;
		case 1: *ret = -radf(x[0],x[2],x[4])+global::sqrt2; break;
		}
		break;


		//Z-con
		default : cout << "unexpected case in constraint " << INEQ_NUMBER<< endl;
		}
    }

iter::iter(int ineqSwitch) {
	numiter = 80; numargs = 6; nconstr=0; // numiter was 20;
	switch(ineqSwitch)
		{
		case 348940660+1 : numargs=16;
		case 97:numargs=13;
		case 98:numargs=16;
		case 99:numargs=16;
		case 117:numargs=9;
		}
	// temp: 
	xmin = new double[numargs];
	xmax = new double[numargs];
	x = new double[numargs];
	constraintfunc = nofunc;
	func = generic;
	int i;
	for (i=0;i<numargs;i++) { xmin[i]=x[i]=2.0; xmax[i]=2.51; }
	INEQ_NUMBER = ineqSwitch;
	switch (ineqSwitch)
		{
		case 348940660+1 :
		xmin[15]=2.51; xmax[15]=global::sqrt8;
		nconstr=2;
		break;

		case 2:
		xmax[0]=2.21; xmax[1]=2.144; xmax[2]=2.245;
		xmin[4]=2.51; xmax[4]=global::sqrt8;
		xmin[3]=2.51; xmax[3]=3.2;
		nconstr=2;
		break;

	        case 91: 
            xmin[3]=2.51; xmax[3]=global::sqrt8;
            nconstr=2;
            break;
        case 92: 
            xmin[3]=2.6; xmax[3]=global::sqrt8;
            xmin[0]=2.2;
            break;
        case 93: 
            xmin[3]=2.7; xmax[3]=global::sqrt8;
            xmax[0]=2.2;
            break;
        case 94: 
            xmin[3]=2.51; xmax[3]=global::sqrt8;
            nconstr=1;
            break;
		case 95: 
            xmin[3]=2.51; xmax[3]=global::sqrt8;
            nconstr=1;
            break;
		case 96:
			xmin[3]=xmax[3]=global::sqrt8;
			xmin[5]=2.51; xmax[5]=global::sqrt8;
			break;
		case 97:
			xmin[12]=2.51; xmax[12]=global::sqrt8;
			nconstr=1;
			break;
		case 98:
			xmin[15]=xmax[15]=2.7;
			nconstr=1;
			break;
		case 99:
			xmin[15]=2.51; xmax[15]=global::sqrt8;
			nconstr=7;
			break;
		case 100:
			xmin[0]=2.51; xmax[0]=global::sqrt8;
			xmin[0]=2.696;
			xmin[3]=2.1;
			break;
		case 101:
			xmin[0]=2.51; xmax[0]=2.696;
			break;
		case 102:
			xmin[0]=2.51; xmax[0]=2.696;
			nconstr=1;
			break;
		case 103:
			xmin[3]=2.51; xmax[3]=global::sqrt8;
			xmax[0]=xmax[1]=xmax[2]=2.1;
			nconstr=2;
			break;
		case 104:
			xmax[3]=xmax[4]=xmax[5]=2.;
			xmin[0]=2.51; xmax[0]=2.7;
			xmin[1]=2.51; xmax[1]=2.7;
			nconstr=1;
			break;
		case 105:
			xmin[4]=2.51; xmax[4]=2.77; //global::sqrt8;
			xmin[5]=2.51; xmax[5]=2.77; //2.77; xmax[5]=global::sqrt8;
			//nconstr=1;
			break;
		case 106:
			xmin[3]=2.51; xmax[3]=global::sqrt8;
			xmax[4]=xmax[5]=2.3;
			xmax[0]=xmax[1]=xmax[2]=2.1;
			nconstr=1;
			break;
		case 107:
			xmin[3]=2.51; xmax[3]=2.7;
			nconstr=1;
			break;
		case 108:
			xmax[3]=xmax[4]=xmax[5]=2.;
			xmin[0]=2.51; xmax[0]=2.57;
			xmax[1]=xmax[2]=2.25;
			//nconstr=1;
			break;
		case 109:
			xmax[4]=xmax[5]=2.3;
			xmin[3]=2.51; xmax[3]=global::sqrt8;
			nconstr=1;
			break;
		case 110:
			xmin[3]=2.51; xmax[3]=global::sqrt8;
			nconstr=2;
			break;
		case 111:
			xmin[0]=2.696; xmax[0]=global::sqrt8;
			xmin[1]=xmin[5]=2.45;
			break;
		case 112:
			xmin[0]=2.45;
			break;
		case 113:
			xmin[0]=2.696; xmax[0]=global::sqrt8;
			xmin[3]=global::sqrt8; xmax[3]=3.2;
			xmin[1]=2.45; xmin[5]=2.45;
			break;
		case 114:
			xmin[1]=2.45;
			xmin[3]=global::sqrt8; xmax[3]=3.2;
			break;
		case 115:
			xmin[0]=2.51; xmax[0]=2.696;
			xmin[3]=2.51; xmax[3]=global::sqrt8;
			break;
		case 116:
			xmin[0]=xmax[0]=2.696;
			xmin[2]=2.51;
			xmax[3]=2.;
			xmin[4]=2.51; xmax[4]=3.17;
			xmin[5]=xmax[5]=2.;
			break;
		case 117:
			xmin[1]=xmax[1]=2.;
			xmin[2]=xmax[2]=2.696;
			xmin[3]=2.51; xmax[3]=3.17;
			xmin[4]=xmax[4]=2.;
			xmin[5]=xmax[5]=2.;
			xmin[8]=xmax[8]=2.;
			nconstr=2;
			break;
		case 118:
			xmax[3]=3.2;
			xmin[4]=xmax[4]=xmin[5]=xmax[5]=2.51;
			break;
		case 119:
			xmax[3]=3.2;
			xmin[4]=xmax[4]=3.2;
			xmin[5]=xmax[5]=2.;
			xmin[0]=2.2;
			break;

		case 355:
			xmin[0]=2.51;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.51;
xmax[3]=2.255;
xmax[4]=2.51;
xmax[5]=2.255;
			nconstr=1;
			break;

		case 617:
			xmin[0]=2.669213562;
xmin[1]=2.255;
xmin[2]=2;
xmin[3]=2.255;
xmin[4]=2;
xmin[5]=2.255;
 
xmax[0]=2.828427125;
xmax[1]=2.3825;
xmax[2]=2.1275;
xmax[3]=2.3825;
xmax[4]=2.1275;
xmax[5]=2.3825;

			nconstr=1;
			break;

case 688:
xmin[0]=2.669213562;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.1275;
xmax[2]=2.1275;
xmax[3]=2.1275;
xmax[4]=2.1275;
xmax[5]=2.1275;

nconstr=1;
break;

case 690:
xmin[0]=2.669213562;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.1275;
xmax[2]=2.1275;
xmax[3]=2.1275;
xmax[4]=2.1275;
xmax[5]=2.1275;

nconstr=1;
break;


case 703:
xmin[0]=2.669213562;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.1275;
xmax[2]=2.1275;
xmax[3]=2.255;
xmax[4]=2.1275;
xmax[5]=2.1275;

nconstr=1;
break;


case 705:
xmin[0]=2.669213562;
xmin[1]=2.1275;
xmin[2]=2;
xmin[3]=2.1275;
xmin[4]=2.1275;
xmin[5]=2.1275;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.1275;
xmax[3]=2.255;
xmax[4]=2.255;
xmax[5]=2.255;

nconstr=1;
break;


case 707:
xmin[0]=2.669213562;
xmin[1]=2.1275;
xmin[2]=2.1275;
xmin[3]=2.1275;
xmin[4]=2;
xmin[5]=2.1275;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.255;
xmax[3]=2.255;
xmax[4]=2.1275;
xmax[5]=2.255;

nconstr=1;
break;
			

case 709:
xmin[0]=2.669213562;
xmin[1]=2.1275;
xmin[2]=2.1275;
xmin[3]=2.1275;
xmin[4]=2.1275;
xmin[5]=2.1275;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.255;
xmax[3]=2.255;
xmax[4]=2.255;
xmax[5]=2.255;

nconstr=1;
break;
			

case 761:
xmin[0]=2.748820344;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.06375;
xmax[2]=2.06375;
xmax[3]=2.06375;
xmax[4]=2.06375;
xmax[5]=2.06375;

nconstr=1;
break;
			

case 765:
xmin[0]=2.748820344;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.06375;
xmax[2]=2.06375;
xmax[3]=2.06375;
xmax[4]=2.06375;
xmax[5]=2.06375;

nconstr=1;
break;
			

case 837:
xmin[0]=2.669213562;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.1275;
xmax[2]=2.1275;
xmax[3]=2.1275;
xmax[4]=2.1275;
xmax[5]=2.1275;
 

nconstr=1;
break;
			

case 859:
xmin[0]=2.51;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.51;
xmax[2]=2.255;
xmax[3]=2.51;
xmax[4]=2.255;
xmax[5]=2.51;

nconstr=1;
break;
			

case 882:
xmin[0]=2.748820344;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.06375;
xmax[2]=2.06375;
xmax[3]=2.06375;
xmax[4]=2.06375;
xmax[5]=2.06375;

nconstr=1;
break;
			

case 899:
xmin[0]=2.748820344;
xmin[1]=2.06375;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.1275;
xmax[2]=2.1275;
xmax[3]=2.1275;
xmax[4]=2.1275;
xmax[5]=2.06375;
nconstr=1;
break;
			

case 969:
xmin[0]=2.669213562;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.255;
xmax[3]=2.255;
xmax[4]=2.255;
xmax[5]=2.255;

nconstr=1;
break;
			

case 972:
xmin[0]=2.51;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.255;
xmax[3]=2.255;
xmax[4]=2.255;
xmax[5]=2.255;

nconstr=1;
break;
			

case 1000:
xmin[0]=2.51;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.51;
xmax[2]=2.51;
xmax[3]=2.51;
xmax[4]=2.51;
xmax[5]=2.51;

nconstr=1;
break;
			

case 1008:
xmin[0]=2.51;
xmin[1]=2;
xmin[2]=2;
xmin[3]=2;
xmin[4]=2;
xmin[5]=2;
 
xmax[0]=2.828427125;
xmax[1]=2.255;
xmax[2]=2.255;
xmax[3]=2.255;
xmax[4]=2.255;
xmax[5]=2.255;

nconstr=1;
break;
			
		//Z-vars
		default : cout << "error " << ineqSwitch << ": not installed " << endl;
		}

	if (nconstr>0) constraintfunc=ConstraintPage1;
	}

void /*ineq.cc*/minimize2(int);

void page1()
	{
	// minimize2(348940660+1);
	/* // an inequality for flat quarters, 4/19/98, 91--95 are together
	minimize2(91);
	minimize2(92);
	minimize2(93);
	minimize2(94);
	minimize2(95);

	minimize2(96);
	minimize2(97); // 3 qrtets & a flat, what is the sum of the opposite edges?
	minimize2(98); // 4 qrtets & a flat, what is the sum of the edges?
	minimize2(99); // 5 simplices of various shapes, ax+b inequality.
	minimize2(100); // 4/26/98, erasing upright above 2.696 diagonal.
	minimize2(101); // 4/27/98, upright<2.696,adapt ExceptUprightEquations.
	minimize2(102); // 4/27/98, vor version of #101.
	minimize2(103); // 4/28/98, flat gamma
	minimize2(104); // 4/28/98, linearize eta.
	minimize2(105); // 4/28/98, VorVc, two edges>2.51.
	minimize2(107); // 4/29/98, flat vorVc, (for hex 156-17-67-6-*)
	minimize2(106); // 4/29/98, flat gamma, (for hex 156-17-67-6-*)
					// 4/29/98, adapted to (hex 156-17-67-1-*)
	minimize2(108); // anchor2-anchor /4/29/98 for Sam's kappa verifications
	minimize2(109); // 5/1/98, flat gamma, two cases.
	minimize2(110); // 5/1/98, flat gamma, two cases.
	minimize2(111); // 5/4/98, VorAnalytic, on ht>2.696.
	minimize2(112); // 5/4/98, Gamma, on ht>2.45. qrtet
	minimize2(113); // 5/4/98, VorVc on ht>2.45, weird quad.
	minimize2(114); // 5/4/98, VorVc on ht>2.45, weird quad.
	minimize2(115); // 5/4/98, VorVc on S_C and related.
	minimize2(116); // 5/5/98, VorVc weird quad. ht=2.696.
	minimize2(117); // 5/5/98, VorVc weird quad. ht=2.696.
	minimize2(118); // new beta ineq for Part IV.
	minimize2(119); // new beta ineq for Part IV.
	*/

	cout<< "RESULTS WITHOUT EITHER FACE CONSTRAINT ";
	minimize2(355); // sam's 18 cases (355,1).
	minimize2(617); // sam's 18 cases (617,2).
	minimize2(688);
	minimize2(690);
	minimize2(703);
	minimize2(705);
	minimize2(707);
	minimize2(709);
	minimize2(761);
	minimize2(765);
	minimize2(837);
	minimize2(859);
	minimize2(882);
	minimize2(899);
	minimize2(969);
	minimize2(972);
	minimize2(1000);
	minimize2(1008);
	}
