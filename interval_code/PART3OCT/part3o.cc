#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"

// global variable used to patch various things for the last 18 cases....
int Final18 = 0;

// global variable used to adjust the constant to try to make the
							// last 18 cases go through.
interval slop("0.0");

static int nearest(double x) 
	{
	return (int)(x< 0 ? ceil(x-0.5) : floor (x+0.5));
	}

static void selfTest()
    {
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    }

int setFTC(double f[2],int T[4],double Dm[13],double DM[13],double C[29],
    int index); // index =0,...,1132.
int setFTCsupp(double f[2],int T[4],double Dm[13],double DM[13],double C[29],
    int index); // index =0,...,206 // subdividing 18 stubborn cases.

int setFTCboth(double f[2],int T[4],double Dm[13],double DM[13],double C[29],
    int index)
	{
	if (Final18) return setFTCsupp(f,T,Dm,DM,C,index);
	else return setFTC(f,T,Dm,DM,C,index);
	}

static int Casenum(int index)
	{
	if (Final18) return 2; // all undone cases 355...1008 fall in case 2.
	if (index<96) { return  0; }
	else if (index <311) { return 1; }
	else if (index <1037) { return 2; }
	else return 3;
	}

static int checkIntegrity(double f[2],int casenum)
	{
	static const double fvalue[4][2]= 
		{{-3.0508,9.494},{-0.27605,1.0472},
		{0.198867,-0.7624},{0.844,-3.5926}};
	if (fabs(f[0]-fvalue[casenum][0])> 1.0e-14) return 0;
	if (fabs(f[1]-fvalue[casenum][1])> 1.0e-14) return 0;
	return 1;
	}

static int PrintIndex(int index) // use this to check data...
	{
	double f[2];int T[4];double Dm[13];double DM[13];double C[29];
	setFTCboth(f,T,Dm,DM,C,index); 
	int casenum = Casenum(index);
	if (!checkIntegrity(f,casenum))
		{
		error::message("bad f parameters");
		return 0;
		}
	cout << T[3]+2*T[2]+4*T[1]+8*T[0] << ": ";
	static const double sqrt8 = 2.8284271247461900976033774;
	static const double t51 = 2.51;
	int segment[13];
	segment[0] = nearest( (sqrt8-t51)/(DM[0]-Dm[0])) ;
	int i;
	for (i=1;i<13;i++)  { segment[i] = nearest(0.51/(DM[i]-Dm[i])); }
	for (i=0;i<13;i++) cout << segment[i] << " "; 
	static double vol = 0.0;
	double prod = 1.0;
	for (i=0;i<13;i++) prod *= segment[i];
	vol += 1.0/( prod);
	cout << " : vol = " << vol << endl;
	return 1;
	}

static int printRecord(int index)
	{
	double f[2];int T[4];double Dm[13];double DM[13];double C[29];
	setFTCboth(f,T,Dm,DM,C,index); 
	int i;
	cout << "\nf = ";
	for (i=0;i<2;i++) cout << f[i] << " ";
	cout << "\nT = ";
	for (i=0;i<4;i++) cout << T[i] << " ";
	cout << "\nDm = ";
	for (i=0;i<13;i++) cout << Dm[i] << " ";
	cout << "\nDM = ";
	for (i=0;i<13;i++) cout << DM[i] << " ";
	cout << "\nC = ";
	for (i=0;i<29;i++) cout << C[i] << " ";
	cout << endl << endl;
	return 1;
	}

	//////////
	// There has been rounding in the file part3oData.cc.
	// We need to reconstruct the rigorous intervals from the
	// rounded data.  The print3o.outCheck file is the verification
	// that all of our reconstructions fit together to give a
	// correct profile.
	// Im and IM are equal to cleaned up versions of Dm^2 and DM^2. 
	//
static void setInterval(const double Dm[13],const double DM[13],
	interval Im[13],interval IM[13])
	{
	static const double t51 = 2.51;
	static const double sqrt8 = 2.8284271247461900976033774;
	static const interval t("2");
	static const interval T51("2.51");
	static const interval SQRT8 = interMath::sqrt(interval("8"));
	static const interval fr("4");
	static const interval s3("6.3001");
	static const interval et("8");
 
	int i;
	double x0[13]={t51,2,2,2,2, 2,2,2,2,2, 2,2,2};
	double z0[13];
	z0[0]=sqrt8; for (i=1;i<13;i++) z0[i]=t51;
	interval X0[13]={T51,t,t,t,t, t,t,t,t,t, t,t,t};
	interval Z0[13];
	Z0[0]=SQRT8; for (i=1;i<13;i++) Z0[i]=T51;
	interval X02[13]={s3,fr,fr,fr,fr, fr,fr,fr,fr,fr, fr,fr,fr};
	interval Z02[13]={et,s3,s3,s3,s3, s3,s3,s3,s3,s3, s3,s3,s3};
 
	int segment[13];
	for (i=0;i<13;i++)  { segment[i] = nearest((z0[i]-x0[i])/(DM[i]-Dm[i])); }
 
	int segN[13];
	for (i=0;i<13;i++) 
		{ segN[i]= nearest (((Dm[i]-x0[i])*segment[i])/(z0[i]-x0[i])); }
	int segU[13];
	for (i=0;i<13;i++) 
		{ segU[i]= nearest (((DM[i]-x0[i])*segment[i])/(z0[i]-x0[i])); }
 
	for (i=0;i<13;i++)
		{
		interval s(segment[i],segment[i]);
		interval n(segN[i],segN[i]);
		interval u(segU[i],segU[i]);
		Im[i]= X0[i]+ (n/s)*(Z0[i]-X0[i]);
		IM[i]= X0[i]+ (u/s)*(Z0[i]-X0[i]);
		}
	for (i=0;i<13;i++)
		{
		Im[i]= Im[i]*Im[i];
		IM[i]= IM[i]*IM[i];
		if (interMath::inf(Im[i])<interMath::inf(X02[i])) 
			{ Im[i].lo = X02[i].lo; }
		if (interMath::sup(Im[i])<interMath::inf(X02[i])) 
			{ error::message("Im out of range");  }
		if (interMath::sup(IM[i])>interMath::sup(Z02[i])) 
			{ IM[i].hi = Z02[i].hi; }
		if (interMath::inf(IM[i])>interMath::inf(Z02[i])) 
			{ error::message("IM out of range");  }
		}
	}

static void testSetInterval(int index)
	{
	double f[2];int T[4];double Dm[13];double DM[13];double C[29];
	setFTCboth(f,T,Dm,DM,C,index); 
	interval Im[13], IM[13];
	setInterval(Dm,DM,Im,IM);
	int i;
	for (i=0;i<13;i++) 
	 cout <<Dm[i]*Dm[i] << " " << Im[i] << endl; cout << endl;
	for (i=0;i<13;i++) 
	 cout <<DM[i]*DM[i] << " " << IM[i] << endl; cout << endl;
	}

static interval I(double x) { return interval(x,x); }

static void setCoefficient(const double C[29],
	interval cc[4],interval cy1[4],interval cy2[4],
	interval cy3[4],interval cy5[4],interval cy6[4],interval cd[4])
	{
	int i;
	for (i=0;i<4;i++) cc[i]=I(C[7*i]);
	for (i=0;i<4;i++) cy1[i]=I(C[1+7*i]); 
	for (i=0;i<4;i++) cy2[i]=I(C[2+7*i]); 
	for (i=0;i<4;i++) cy3[i]=I(C[3+7*i]); 
	for (i=0;i<4;i++) cy5[i]=I(C[4+7*i]); 
	for (i=0;i<4;i++) cy6[i]=I(C[5+7*i]); 
	cd[0]=cd[1]=cd[2]=cd[3]=I(C[6]); //should= C[6+7*i];
	interval t;
	static const interval four("4");
	static const interval two("2");

	t=interval("0"); for (i=0;i<4;i++) t = t+ cc[i];
	if (interMath::sup(t)<0)
		{
		t=interMath::max(t,t);
		t = t/four;
		cout << "adjusted cc by " << -t << endl;
		for (i=0;i<4;i++) cc[i] = cc[i] - t;
		}

	t=interval("0"); for (i=0;i<4;i++) t = t+ cy1[i];
	if (interMath::sup(t)<0)
		{
		t=interMath::max(t,t);
		t = t/four;
		cout << "adjusted cy1 by " << -t << endl;
		for (i=0;i<4;i++) cy1[i] = cy1[i] - t;
		}

	for (i=0;i<4;i++)
	{
	t=cy3[i]+cy2[(i+1) % 4];
	if (interMath::sup(t)<0)
		{
		t=interMath::max(t,t); t = t/two;
		cout << "adjusted cy3 "<<i<<" by " << -t << endl;
		cy3[i] = cy3[i]-t; cy2[(i+1)% 4] = cy2[(i+1)% 4]-t;
		}
	}

	for (i=0;i<4;i++)
	{
	t=cy5[i]+cy6[(i+1) % 4];
	if (interMath::sup(t)<0)
		{
		t=interMath::max(t,t); t = t/two;
		cout << "adjusted cy5 "<<i<<" by " << -t << endl;
		cy5[i] = cy5[i]-t; cy6[(i+1)% 4] = cy6[(i+1)% 4]-t;
		}
	}

	}

static void setFace(const int T[4],int face126[4],int face135[4])
	{
	int i;
	for (i=0;i<4;i++) face126[i]=T[i];
	for (i=0;i<4;i++) face135[i]=T[(i+1) % 4];
	}

static void setDomain(const interval Im[4],const interval IM[4],
	domain x[4],domain z[4])
	{
	double x0[13]; double z0[13];
	int i;
	for (i=0;i<13;i++) x0[i] = interMath::inf(Im[i]);
	for (i=0;i<13;i++) z0[i] = interMath::sup(IM[i]);
	x[0]=domain(x0[0],x0[1],x0[2],x0[3],x0[4],x0[5]);
	z[0]=domain(z0[0],z0[1],z0[2],z0[3],z0[4],z0[5]);
	x[1]=domain(x0[0],x0[2],x0[7],x0[6],x0[8],x0[4]);
	z[1]=domain(z0[0],z0[2],z0[7],z0[6],z0[8],z0[4]);
	x[2]=domain(x0[0],x0[7],x0[11],x0[9],x0[10],x0[8]);
	z[2]=domain(z0[0],z0[7],z0[11],z0[9],z0[10],z0[8]);
	x[3]=domain(x0[0],x0[11],x0[1],x0[12],x0[5],x0[10]);
	z[3]=domain(z0[0],z0[11],z0[1],z0[12],z0[5],z0[10]);
	}

int emptyDomain(interval Im[13],interval IM[13],int T[4])
	{
	double m[13],M[13];
	int i;
	for (i=0;i<13;i++) m[i]=interMath::inf(Im[i]);
	for (i=0;i<13;i++) M[i]=interMath::sup(IM[i]);
	if ((T[0])&&(linearization::eta2(domain(M[0],M[1],0,0,0,M[5])).hi()<2)) return 1;
	if ((T[1])&&(linearization::eta2(domain(M[0],M[2],0,0,0,M[4])).hi()<2)) return 1;
	if ((T[2])&&(linearization::eta2(domain(M[0],M[7],0,0,0,M[8])).hi()<2)) return 1;
	if ((T[3])&&(linearization::eta2(domain(M[0],M[10],0,0,0,M[11])).hi()<2)) return 1;
	if ((!T[0])&&(linearization::eta2(domain(m[0],m[1],0,0,0,m[5])).low()>2)) return 1;
	if ((!T[1])&&(linearization::eta2(domain(m[0],m[2],0,0,0,m[4])).low()>2)) return 1;
	if ((!T[2])&&(linearization::eta2(domain(m[0],m[7],0,0,0,m[8])).low()>2)) return 1;
	if ((!T[3])&&(linearization::eta2(domain(m[0],m[10],0,0,0,m[11])).low()>2)) return 1;
	return 0;
	}

pX(interval u) { cout.precision(10); cout << interMath::inf(u); }


int Verify(int index,int casesToDo[4]) 
	{
	static const interval fvalue[4][2]= 
		{{"-3.0508","9.494"},{"-0.27605","1.0472"},
		{"0.198867","-0.7624"},{"0.844","-3.5926"}};
	double f[2];int T[4];double Dm[13];double DM[13];double C[29];
	setFTCboth(f,T,Dm,DM,C,index);
	int casenum = Casenum(index);
	interval Im[13],IM[13];
	setInterval(Dm,DM,Im,IM);
	interval cc[4],cy1[4],cy2[4],cy3[4],cy5[4],cy6[4],cd[4];
	setCoefficient(C,cc,cy1,cy2,cy3,cy5,cy6,cd);
	domain x[4],z[4];
	setDomain(Im,IM,x,z);
	// check domain....
	if (emptyDomain(Im,IM,T))
		{
		cout << "\ncase("<<index<<")" << endl << flush;
		error::printTime(" done! (empty domain) ");
		return 1;
		}
	taylorFunction DIH[4]=
		{taylorUpright::dih2+taylorUpright::dih3,
		 taylorUpright::dih2,
		 taylorSimplex::unit*"0",
		 taylorUpright::dih3};
	char* DIHtext[4]={"(dih2+dih3)","dih2","0","dih3"};
	static const interval pi2("1.5707963267948966192");
	taylorFunction dpi = taylorUpright::dih+taylorSimplex::unit*(-pi2);
	taylorFunction G126[2]=
		 {taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2",
		 taylorSimplex::eta2_126 + taylorSimplex::unit*"-2"};
	taylorFunction H135[2]=
		 {taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2",
		 taylorSimplex::eta2_135 + taylorSimplex::unit*"-2"};
	int i;
	for (i=0;i<4;i++)
	{
	if (!casesToDo[i]) 
		{
		cout << "skipping " << i << endl;
		continue;
		}
	domain x0 = x[i],z0 = z[i];
	int face126[4],face135[4];
	setFace(T,face126,face135);
	taylorFunction sig = 
		(face126[i]||face135[i] ? 
			taylorUpright::octavor : taylorUpright::gamma);
	static const interval four("4");
	taylorFunction Fsig = sig +taylorSimplex::unit*(fvalue[casenum][1]/four)
		+ DIH[i]*(fvalue[casenum][0]);
	taylorFunction F = Fsig 
		+ taylorSimplex::unit*cc[i]
		+ taylorSimplex::unit*(-slop)
		+ taylorSimplex::y1*cy1[i]
		+ taylorSimplex::y2*cy2[i]
		+ taylorSimplex::y3*cy3[i]
		+ taylorSimplex::y5*cy5[i]
		+ taylorSimplex::y6*cy6[i]
		+ dpi*cd[i];
	// if face126==0, then it is small, so add ||Big126
	// if face126==1, then it is big, so add ||Small126.
	taylorFunction G = G126[face126[i]];
	taylorFunction H = H135[face135[i]];
    const taylorFunction* I[3] = {&F,&G,&H};
    cellOption opt;
	cout << "\n\ncase("<<index<<"," << i <<")" << endl << flush;
	int j;
	cout.precision(10);
	cout << "\ndouble Fsig = sig + ("; pX(fvalue[casenum][1]/four); 
		cout<<") + "<<DIHtext[i]
		<< "*("; pX(fvalue[casenum][0]); cout << ");" << endl;
	cout << "double F = Fsig+ "; pX(cc[i]); cout<< "+y1*("; pX(cy1[i]);
			cout <<") ";
	cout << "+y2*("; pX(cy2[i]); cout << ") ";
	cout << "+y3*("; pX(cy3[i]); cout << ") ";
	cout << "+y5*("; pX(cy5[i]); cout << ") ";
	cout << "+y6*("; pX(cy6[i]); cout << ") ";
	cout<< "+(dih1-pi/2)*("; pX(cd[i]); cout << ");";
	cout << "\nsig = ";
	cout << (face126[i]||face135[i]? "octavor" : "gamma") << endl;
	cout << endl;
	cout.precision(10);
    for (j=0;j<6;j++) cout << "xmin["<<j<<"]="<<sqrt(x0.getValue(j)) << ";\n";
	cout << endl;
	for (j=0;j<6;j++) cout << "xmax["<<j<<"]="<<sqrt(z0.getValue(j)) << ";\n";
	cout << endl;
	cout << " f(126,135)=" << face126[i] << " " << face135[i] << endl;
	cout << " (0 means small face, 1 means large face) " << endl;
	return 1;
	cout << " coeff(c,y1,y2,y3,y5,y6,dih,f0,f1)= ";
	cout << cc[i] << " " << cy1[i] << " " << cy2[i] << " " << cy3[i] << " ";
	cout << cy5[i]<< " " << cy6[i] << " " << cd[i] << " ";
	cout << fvalue[casenum][0] << " " <<fvalue[casenum][1] << endl << flush;
	cout << "endcase." << endl << endl;
	opt.setIterationLimit(5000000); // added 12/31/97 // was 10^6;
	opt.setRecursionDepth(30); // added 1/2/98.
    if (!prove::recursiveVerifier(0,x[i],z[i],x0,z0,I,3,opt)) 
		{
		cout << " failed.\n";
		return 0;
		}
	cout << " done!" << endl;
	}
	error::printTime("case complete");
	return 1;
	}

main()
	{
	selfTest();
	//printRecord(200);
	//testSetInterval(200);
	if (Final18) cout << "Final 18 parameter is set" << endl;
	else cout << "Final 18 parameter is not set" << endl;
	cout << "slop factor in verifications= " << slop << endl;
	int i;
	int remainder[18]= // list comes from part3o.fail.
		{355,617,688,690,703,705,707,709,761,765,837,859,
		 882,899,969,972,1000,1008};
	int whichCases[18]= // from part3o.fail.
		{1 ,2 ,0 ,1 ,3 ,2 ,2 ,2 ,0 ,0 ,0 ,3 ,1 ,1 ,2 ,1 ,2 ,0};
	for (i=0;i<18;i++) 
		{
		int casesToDo[4]={0,0,0,0};
		casesToDo[whichCases[i]]=1;
		Verify(remainder[i],casesToDo);
		}

	/*
	int casesToDo[4]={1,1,1,1};
	for (i=181;i<207;i++) Verify(i,casesToDo);
	*/


	error::printTime();
	}
