// Cut from secondDerive.cc on 5/22/98.
// These procedures are not needed for the day-to-day use of secondDerive.cc

	//////////
	// Start here with procedures used to bound the second derivatives in SECOUT
	// These procedures only need to be run once.
	// 
static void report(const char* function,const char* region,const double x[6],
	const double w[6],const interval DD[6][6])
	{
	int i,j;
	double xx[6][6];
	// now report:
	cout << endl << endl << flush;
	cout << function << " second partial bounds on a " << region << endl << flush;
	cout << "x in " << flush;
	cout.precision(10);
	for (i=0;i<6;i++) cout << "[" << x[i] << "," << x[i]+20.0*w[i] << "]" << flush;
	cout << endl << flush;
	cout.precision(20);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		{
		cout << function << region[0] << "[" << i << "," << j << "]= " << flush;
		cout << (xx[i][j]=interMath::sup(interMath::max(DD[i][j],-DD[i][j]))) << endl << flush;
		}
	double total=0.0;
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		total = total + xx[i][j];
	cout << "The 36 second absolute partials of " << flush;
	cout << function << " sum to  " << total << endl << flush;
	total = 0.0;
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		if (xx[i][j]>total) total = xx[i][j];
	cout << "the max abs value is " << total << endl << flush;
	}

static void symmetrize(interval DD[6][6]) // because x1<x2;
	{
	int k[6] = {0,2,1,3,5,4};
	int i;
        for (i=0;i<6;i++)
			{
			DD[i][1]=DD[1][i]=DD[k[i]][k[1]]=DD[k[1]][k[i]]=
							interMath::combine(DD[i][1],DD[k[i]][k[1]]);
			DD[i][4]=DD[4][i]=DD[k[i]][k[4]]=DD[k[4]][k[i]]=
							interMath::combine(DD[i][4],DD[k[i]][k[4]]);
		}
	}

void quasiregular_partition() // Used to generate 2nd d. bounds.
	{
	static const interval zero("0");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	interval t63001 = "6.3001";
	double x0[6],z0[6];
	int i,j;
	for (i=0;i<6;i++) { x0[i] = 4.0; z0[i] = 4.0;  }
 
	//INITIALIZATION 
	static const interval N20("20");
	static const interval eps1 = (t63001-four)/N20;
	//interval eps0 = (eight-t63001)/N20;
 
	double w[6]; for (i=0;i<6;i++) w[i] = interMath::sup(eps1); 
	double wn[6]; for (i=0;i<6;i++) wn[i] = interMath::inf(eps1); 
 
	//x0[3] = interMath::inf(t63001); z0[3]= interMath::sup(t63001);
	//w[3] = interMath::sup(eps0); wn[3] = interMath::inf(eps0);
	const char* runtype = "quasiregular tet";
	double x[6],z[6];
 
	interval fDDx[6][6],DDx[6][6],fDDy[6][6],DDy[6][6];
	interval di,Ddi[6],DDdi[6][6],fDDdi[6][6]; // dihedral;
	interval sqrt_d,Dsqrt_d[6],DDsqrt_d[6][6],fDDs[6][6];
	interval DDVc[6][6], fDDVc[6][6];
	interval DDc[6][6], fDDc[6][6];
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		{ fDDx[i][j]=zero; fDDy[i][j]=zero; 
		  fDDdi[i][j]=zero; fDDs[i][j]=zero; 
		  fDDVc[i][j]=fDDc[i][j]=zero;
		}
	interval b = zero,s=zero;
	interval trunc0 = interval("1.255");
	interval trunc1 = interMath::sqrt(two);
	
	//LOOP
	int k[6];
	int top = 20; // MUST BE 20 to BE compatible with report;
	int count=0;
	for (k[0]=0;k[0]<top;k[0]++)
	for (k[1]=0;k[1]<top;k[1]++) 
	for (k[2]=k[1];k[2]<top;k[2]++) // make use of symmetry
	for (k[3]=0;k[3]<top;k[3]++)
	for (k[4]=0;k[4]<top;k[4]++)
	for (k[5]=0;k[5]<top;k[5]++)
		{
		if ((k[2]==k[1])&&(k[4]<k[5])) continue;//degenerate symmetry.
		//POOL
		interMath::up(); for (j=0;j<6;j++) z[j]=z0[j]+double(k[j]+1)*w[j];
		interMath::down(); for (j=0;j<6;j++) x[j]=x0[j]+double(k[j])*wn[j];
		if (!secondDerive::setSqrtDelta(x,z,sqrt_d,Dsqrt_d,DDsqrt_d))
			error::message("bad sqrt delta");
		vorAnalytic34(x,z,sqrt_d,Dsqrt_d,DDsqrt_d,DDx,DDy);
		secondDerive::setDihedral(x,z,sqrt_d,Dsqrt_d,DDsqrt_d,di,Ddi,DDdi);
		Adih(x[0],z[0],trunc0,di,Ddi,DDdi,DDVc);
		Adih(x[0],z[0],trunc1,di,Ddi,DDdi,DDc);
 
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			{
			fDDx[i][j]=interMath::combine(fDDx[i][j],DDx[i][j]);
			fDDy[i][j]=interMath::combine(fDDy[i][j],DDy[i][j]);
			fDDdi[i][j]=interMath::combine(fDDdi[i][j],DDdi[i][j]);
			fDDs[i][j]=interMath::combine(fDDs[i][j],DDsqrt_d[i][j]);
			fDDVc[i][j]=interMath::combine(fDDVc[i][j],DDVc[i][j]);
			fDDc[i][j]=interMath::combine(fDDc[i][j],DDc[i][j]);
			}
		/* // for chi234 only:
		setChi234(x,z,di,Ddi,DDc);
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			{
			fDDc[i][j]=interMath::combine(fDDc[i][j],DDc[i][j]);
			}
		*/
 
		if (0 == (count++ % 1000000)) //  should be every million
			{
			for (i=0;i<6;i++) for (j=0;j<6;j++)
				{
				b = interMath::combine(fDDx[i][j],b);
				s = interMath::combine(fDDy[i][j],s);
				}
			cout << k[0] << " " << k[1] << " " << k[2] << " " << k[3] << " " << k[4] << flush;
			cout << " " << k[5] << " " << flush; 
			cout << band((four/three)*b) << band(s) << endl << flush;
			}
		}
 
	// OUTPUT:
 
	// symmetrize; because x1<x2;
	symmetrize(fDDx);
	symmetrize(fDDy);
	symmetrize(fDDdi);
	symmetrize(fDDs);
	symmetrize(fDDVc);
	symmetrize(fDDc);
 
	// report output.
	cout << "finished " << endl << flush;
	for (i=0;i<6;i++) for (j=0;j<6;j++)  // vorAn34 -> vorAn
		{
		fDDx[i][j] = (four/three)*fDDx[i][j]; 
		}
	report("VORAN",runtype,x0,w,fDDx);
	report("SOL",runtype,x0,w,fDDy);
	report("DIH",runtype,x0,w,fDDdi);
	report("DIHVc",runtype,x0,w,fDDVc);
	report("DIHc",runtype,x0,w,fDDc);
	report("SQRTDELTA",runtype,x0,w,fDDs);
	// report("CHI234",runtype,x0,w,fDDc);  // for chi only
	cout << flush;
	} // end of proc

void dih2_partition() // used to generate 2nd derivative bounds
	{
	static const interval zero("0");
	static const interval two("2");
	static const interval four("4");
	interval t63001 = "6.3001";
	double x0[6],z0[6];
	int i,j;
	for (i=0;i<6;i++) { x0[i] = 4.0; z0[i] = 4.0;  }
 
	//INITIALIZATION 
	static const interval N20("20");
	static const interval N8("8");
	static const interval eps1 = (t63001-four)/N20;
	interval eps0 = (N8-t63001)/N20;
 
	double w[6]; for (i=0;i<6;i++) w[i] = interMath::sup(eps1); 
	double wn[6]; for (i=0;i<6;i++) wn[i] = interMath::inf(eps1); 
 
	// CHANGES HERE 
	x0[3] = interMath::inf(t63001); z0[3]= interMath::sup(t63001);
	w[3] = interMath::sup(eps0); wn[3] = interMath::inf(eps0);
	const char* runtype = "flat quarter";
	double x[6],z[6];
 
	interval di,Ddi[6],DDdi[6][6],fDDdi[6][6]; // dihedral;
	interval DDVc[6][6], fDDVc[6][6];
	interval DDc[6][6], fDDc[6][6];
	cout << runtype << endl << flush;
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		{ 
		  fDDdi[i][j]=fDDVc[i][j]=fDDc[i][j]=zero;
		}
	interval trunc0 = interval("1.255");
	interval trunc1 = interMath::sqrt(two);
	interval b=zero;
	interval s,Ds[6],DDs[6][6];
	
	//LOOP
	int k[6];
	int top = 20; // 20;    // MUST BE 20 to BE compatible with report;
	int count=0;
	for (k[0]=0;k[0]<top;k[0]++)
	for (k[1]=0;k[1]<top;k[1]++) 
	for (k[2]=0;k[2]<top;k[2]++) // no symmetry for dih2; 
	for (k[3]=0;k[3]<top;k[3]++)
	for (k[4]=0;k[4]<top;k[4]++)
	for (k[5]=0;k[5]<top;k[5]++)
		{
 
		//POOL
		interMath::up(); for (j=0;j<6;j++) z[j]=z0[j]+double(k[j]+1)*w[j];
		interMath::down(); for (j=0;j<6;j++) x[j]=x0[j]+double(k[j])*wn[j];
		if (!secondDerive::setSqrtDelta(x,z,s,Ds,DDs)) error::message("bad sqrtdel");
		secondDerive::setDih2(x,z,s,Ds,DDs,di,Ddi,DDdi);
		Adih2(x[1],z[1],trunc0,di,Ddi,DDdi,DDVc);
		Adih2(x[1],z[1],trunc1,di,Ddi,DDdi,DDc);
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			{
			fDDdi[i][j]=interMath::combine(fDDdi[i][j],DDdi[i][j]);
			fDDVc[i][j]=interMath::combine(fDDVc[i][j],DDVc[i][j]);
			fDDc[i][j]=interMath::combine(fDDc[i][j],DDc[i][j]);
			}
 
		if (0 == (count++ % 1000000)) // should be every million
			{
			for (i=0;i<6;i++) for (j=0;j<6;j++)
				{
				b = interMath::combine(fDDdi[i][j],b);
				}
			cout << k[0] << " " << k[1] << " " << k[2] << " " << k[3] << " " << k[4] << flush;
			cout << " " << k[5] << " " << flush; 
			cout << band(b) << endl << flush;
			}
		}
 
	// OUTPUT:

 
    // report output.
    cout << "finished " << endl << flush;
    report("DIH2",runtype,x0,w,fDDdi);
    report("DIH2Vc",runtype,x0,w,fDDVc);
    report("DIH2c",runtype,x0,w,fDDc);
    cout << flush;
    } // end of proc
 
 


/*
int crownV(double x,double z,interval& v,interval& Dv,interval& DDv)
	{
	static const interval one("1");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	interval v1,Dv1,DDv1,  v2,Dv2,DDv2;
	// c0 = 8 pi doct 1.255^3/3.
	static const interval s63("6.3001");
	if (z>10.3) return 0;  // triangle assumed to be acute.
	interval h,Dh,DDh;
	nu = interval(x,z);
	h = sqrt(nu);
	Dh = one/(four*h);
	DDh = -Dh/(two*nu);
	h = h/two;
 
	interval u,Du,DDu; // UU(x1,x2,x6)...
	DDu = -two;
	interMath::up();
	Du.hi = 8.0 + 2.0*interMath::sup(s63) + 2.0*(-x);
	interMath::down();
	Du.lo = 8.0 + 2.0*interMath::inf(s63) + 2.0*(-z);
	// Du>0 so use monotonicity:
	static const interval N16("16");
	static const interval N8("8");
	static const interval u0 = -N16+N8*s63 -s63*s63;
	static const interval u1 = N8 + two*s63;
	interMath::up();
	u.hi = interMath::sup(u0) + interMath::sup(u1)*z + z*(-z);
	u.lo = interMath::inf(u0) + interMath::inf(u1)*x + x*(-x);
	static const interval num0 = four*s63;
	interval n,Dn;
	n = num0*nu;
	Dn = num0;
	interval t2,Dt2,DDt2; 
	interval u2 = u*u;
	t2 = n/u;
	Dt2 = (Dn*u- Du*n)/u2;
	DDt2 = -n*DDu/u2 - Du*Dt2/u;
 
	interval t,Dt,DDt;  // t = radf(2,2.51,y1);
	t = interMath::sqrt(t2);
	Dt = Dt2/(two*t);
	DDt = DDt2/(two*t) - Dt*Dt2/(two*t2);  
 
	static const interval c1("11.9378628418071406381771620627");
	// (1-h/t)*c1
	v1 = (one-h/t)*c1;
	Dv1 = -c1*(Dh*t-Dt*h)/t2;
	DDv1 = -two*Dv1*Dt/t - c1*(DDh*t-DDt*h)/t2;
 
	static const interval c2("3.01971121354037588808959323108");
	// c2 = 4/3 doct Pi.
	v2 = c1*h*(h*h-t2);
	Dv2 = c1*(three*h*h*Dh - Dh*t2 - h*Dt2);
	DDv2 = c1*(six*h*Dh*Dh + three*h*h*DDh - DDh*t2-two*Dh*Dt2-h*DDt2);
 
	v = v1+v2;
	Dv = Dv1+Dv2;
	DDv = DDv1+DDv2;
	}
*/


/*
static void setChi234(const double x[6],const double z[6],
	interval& f,interval Df[6],interval DDf[6][6])
	{
	double xx[6],zz[6];
	interval Dg[6],DDg[6][6];
	int k[6]={2,1,0,5,4,3};
	int i,j;
	for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]]; }
	setChi126(xx,zz,f,Dg,DDg);
	for (i=0;i<6;i++) Df[i]= Dg[k[i]];
	for (i=0;i<6;i++) for (j=0;j<6;j++) DDf[i][j]=DDg[k[i]][k[j]];
	}
*/

