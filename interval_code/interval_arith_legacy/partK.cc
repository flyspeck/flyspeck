#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"
 
// stuff for truncation....
 
void selfTest()
    {
	static int i=0;
	if (i>0) { 
		error::printTime();
		error::diagnostic(); 
		cout << endl << endl; }
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
	cout << " -- Installation complete -- " << endl;
	i++;
    }

taylorFunction gammaNu = 
	taylorUpright::gamma + taylorUpright::vorVc*"0.5"
		+taylorUpright::swapVorVc*"-0.5";

taylorFunction vorNu = 
	taylorUpright::vor*"0.5"+taylorUpright::swapVor*"0.5" 
		+ taylorUpright::vorVc*"0.5" +taylorUpright::swapVorVc*"-0.5";

static interval zetapt = "0.10044457142705639500";
taylorFunction tauVNu = vorNu*"-1"+taylorUpright::sol*zetapt;
taylorFunction tauGNu = gammaNu*"-1"+taylorUpright::sol*zetapt;

taylorFunction highTauVc 
	=taylorSimplex::highVorVc*"-1"+taylorSimplex::sol*zetapt;
taylorFunction tauAnalytic = taylorSimplex::vor*"-1"+taylorSimplex::sol*zetapt;

static void setupright(domain& x,domain& z,domain& x0,domain& z0)
    {
    interval tx[6]={"6.3001","4","4","4","4","4"};
    interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
    x = domain::lowerD(tx);
    x0 = domain::lowerD(tx);
    z = domain::upperD(tz);
    z0 = domain::upperD(tz);
    }

static void setC(domain& x,domain& z,domain& x0,domain& z0)
    {
    interval tx[6]={"6.3001","4","4","6.3001","4","4"};
    interval tz[6]={"8","6.3001","6.3001","8","6.3001","6.3001"};
    x = domain::lowerD(tx);
    x0 = domain::lowerD(tx);
    z = domain::upperD(tz);
    z0 = domain::upperD(tz);
    }

static void setANC(domain& x,domain& z,domain& x0,domain& z0)
    {
    interval tx[6]={"6.3001","4","4","8","4","4"};
    interval tz[6]={"8","6.3001","6.3001","10.24","6.3001","6.3001"};
    x = domain::lowerD(tx);
    x0 = domain::lowerD(tx);
    z = domain::upperD(tz);
    z0 = domain::upperD(tz);
    }

static void setLower(domain& x,interval x1,interval x2,interval x3,
		interval x4,interval x5,interval x6)
	{
	interval tx[6]={x1,x2,x3,x4,x5,x6};
	x = domain::lowerD(tx);
	}

static void setUpper(domain& x,interval x1,interval x2,interval x3,
		interval x4,interval x5,interval x6)
	{
	interval tx[6]={x1,x2,x3,x4,x5,x6};
	x = domain::upperD(tx);
	}

// a small variation of prove::generic
int generic2(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[2] = {&F,&G};
    cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt);
    }

// a small variation of prove::generic
int generic2dih(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G,double d)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[2] = {&F,&G};
    cellOption opt;
	opt.setDihMax(d);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt);
    }

// a small variation of prove::generic
int generic3(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G,
    taylorFunction& H)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[3] = {&F,&G,&H};
    cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt);
    }

// a small variation of prove::generic
int genericFlatSigma(const taylorFunction& F)
    {
	// Used in 4.4.
	interval tx("6.3001");
	interval x[6]={"4","4","4",tx,"4","4"};
	interval z[6]={tx,tx,tx,"8",tx,tx};
 
	/* gamma */ {
	taylorFunction Fx = taylorFlat::gamma+ F;
	taylorFunction H1 = taylorSimplex::eta2_234*"-1" + taylorSimplex::unit*"2";
	taylorFunction H2 = taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
	if (!generic3(domain::lowerD(x),domain::upperD(z),Fx,H1,H2))
		{ return 0; }
	cout << "fs: gamma done" << "\n";
	}
 
	/* vor */ {
	taylorFunction Fx = taylorFlat::vor+ F;
	taylorFunction H1 = taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
	if (!generic2(domain::lowerD(x),domain::upperD(z),Fx,H1))
		{ return 0; }
	cout << "fs: vor done" << "\n";
	}
 
	/* vorVc */ {
	interval xc[6]={"4.84","4","4","6.76","4","4"};
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	if (!prove::generic(domain::lowerD(xc),domain::upperD(z),Fx))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	/* vorVc */ {
	interval xc[6]={"4","4","4","7.29","4","4"};
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	if (!prove::generic(domain::lowerD(xc),domain::upperD(z),Fx))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	/* vorVc */ {
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	taylorFunction H1 = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
	if (!generic2(domain::lowerD(x),domain::upperD(z),Fx,H1))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	return 1;
	}


// a small variation of prove::generic
int genericFlatSigmaX(const taylorFunction& F,interval x[6],interval z[6])
    {
	// Used in A.4.12.
 
	/* gamma */ {
	taylorFunction Fx = taylorFlat::gamma+ F;
	taylorFunction H1 = taylorSimplex::eta2_234*"-1" + taylorSimplex::unit*"2";
	taylorFunction H2 = taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
	if (!generic3(domain::lowerD(x),domain::upperD(z),Fx,H1,H2))
		{ return 0; }
	cout << "fs: gamma done" << "\n";
	}
 
	/* vor */ {
	taylorFunction Fx = taylorFlat::vor+ F;
	taylorFunction H1 = taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
	if (!generic2(domain::lowerD(x),domain::upperD(z),Fx,H1))
		{ return 0; }
	cout << "fs: vor done" << "\n";
	}
 
	/* vorVc */ {
	interval xc[6]={"4.84","4","4","6.76","4","4"};
	for (int i=0;i<6;i++) if (xc[i]<x[i]) xc[i]=x[i];
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	if (!prove::generic(domain::lowerD(xc),domain::upperD(z),Fx))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	/* vorVc */ {
	interval xc[6]={"4","4","4","7.29","4","4"};
	for (int i=0;i<6;i++) if (xc[i]<x[i]) xc[i]=x[i];
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	if (!prove::generic(domain::lowerD(xc),domain::upperD(z),Fx))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	/* vorVc */ {
	taylorFunction Fx = taylorSimplex::lowVorVc+ F;
	taylorFunction H1 = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
	if (!generic2(domain::lowerD(x),domain::upperD(z),Fx,H1))
		{ return 0; }
	cout << "fs: vorVc done" << "\n";
	}
 
	return 1;
	}



void verify(int identifier) 
	{
	cout << "Begin verification of " << identifier << endl;
	error::printTime();
	int t;
	switch(identifier)
		{
		// Section A1:

		case 269048407:
			{
			interval ts("7.268416"); // 2.696^2
			interval tx("6.3001");
			interval x[6]={ts,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = gammaNu
				+taylorUpright::vorVc*"-1"
				+taylorUpright::dih*"0.01"
				+taylorSimplex::unit*"-0.0157079632679489661923";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }	
			cout << "gammaNu done\n";
			taylorFunction F2 = vorNu
				+taylorUpright::vorVc*"-1"
				+taylorUpright::dih*"0.01"
				+taylorSimplex::unit*"-0.0157079632679489661923";
			taylorFunction G = 
              taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			t = generic2(domain::lowerD(x),domain::upperD(z),F2,G);
			}
			break;

		case 553285469:
			{
			interval ts("7.268416"); // 2.696^2
			interval tx("6.3001");
			interval x[6]={"6.76","4","4","4.41","4","4"};
			interval z[6]={ts,tx,tx,tx,tx,tx};
			taylorFunction F = gammaNu
				+taylorUpright::vorVc*"-1";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }	
			cout << "gammaNu done\n";
			taylorFunction F2 = vorNu
				+taylorUpright::vorVc*"-1";
			taylorFunction G = 
              taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			t = generic2(domain::lowerD(x),domain::upperD(z),F2,G);
			}
			break;

		case 293389410:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F = taylorFlat::gamma
				+taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"-0.0268";
			taylorFunction G = 
              taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }	
			cout << "gamma done\n";
			taylorFunction F2 = taylorFlat::vor
				+taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"-0.0268";
			taylorFunction G2 = 
              taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			t=generic2(domain::lowerD(x),domain::upperD(z),F2,G2);
			}
			break;

		case 695069283:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={"4.7089",tx,tx,"8",tx,tx};
			taylorFunction F = taylorFlat::gamma
				+taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"-0.02";
			taylorFunction G = 
              taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }	
			cout << "gamma done\n";
			taylorFunction F2 = taylorFlat::vor
				+taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"-0.02";
			taylorFunction G2 = 
              taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			t=generic2(domain::lowerD(x),domain::upperD(z),F2,G2);
			}
			break;

		case 814398901:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F = taylorFlat::dih*"-1"
				+taylorSimplex::unit*"1.32";
			t=prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 352079526:
			{

			interval pt("0.055373645668463869730");
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
		    taylorFunction tauVc = taylorSimplex::lowVorVc*"-1"
                +taylorFlat::sol*zetapt;
		    taylorFunction tauG = taylorFlat::gamma*"-1"
                +taylorFlat::sol*zetapt;
		    taylorFunction tauV = taylorFlat::vor*"-1"
                +taylorFlat::sol*zetapt;
			taylorFunction FVc = tauVc*"-1"
				+taylorSimplex::unit*(interval("3.07")*pt);
			taylorFunction FV = tauV*"-1"
				+taylorSimplex::unit*(interval("3.07")*pt);
			taylorFunction FG = tauG*"-1"
				+taylorSimplex::unit*(interval("3.07")*pt);
			taylorFunction dihEqn =
				taylorFlat::dih*"-1"
				+taylorSimplex::unit*"1.32";

			/* gamma */{
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&FG,&dihEqn};
			cellOption opt;
			if (!prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,2,opt))
				{ t = 0; break; }
			cout << "gamma done\n";
			}

			/* vor */{
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			taylorFunction G = 
              taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			const taylorFunction* I[3] = {&FV,&G,&dihEqn};
			cellOption opt;
			if (!prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,3,opt))
				{ t = 0; break; }
			cout << "vor done\n";
			}

			/* vorVc, 2.2 */{
			interval xA[6]={"4.84","4","4","6.76","4","4"};
			domain x0 = domain::lowerD(xA),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&FVc,&dihEqn};
			cellOption opt;
			if (!prove::recursiveVerifier(0,domain::lowerD(xA),
									domain::upperD(z),x0,z0,I,2,opt))
				{ t = 0; break; }
			cout << "vorVc done\n";
			}

			/* vorVc, 2.7 */{
			interval xA[6]={"4","4","4","7.29","4","4"};
			domain x0 = domain::lowerD(xA),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&FVc,&dihEqn};
			cellOption opt;
			if (!prove::recursiveVerifier(0,domain::lowerD(xA),
									domain::upperD(z),x0,z0,I,2,opt))
				{ t = 0; break; }
			cout << "vorVc done\n";
			}

			/* vorVc, etatop */{
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			taylorFunction G = 
              taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			const taylorFunction* I[3] = {&FVc,&G,&dihEqn};
			cellOption opt;
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,3,opt);
			}

			}
			break;

		case 179025673:
			{
			interval pt("0.055373645668463869730");
			interval xiV("0.003521");
			interval xiGp("0.00935");
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
		   taylorFunction tauVc = taylorSimplex::lowVorVc*"-1"
                +taylorFlat::sol*zetapt;
			taylorFunction F = tauVc*"-1"
				+taylorSimplex::unit*
					(interval("3.07")*pt + xiV+xiGp*"2.0");
			taylorFunction dihEqn =
				taylorFlat::dih*"-1"
				+taylorSimplex::unit*"1.32";

			/* vorVc, etatop */{
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			taylorFunction G = 
              taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			const taylorFunction* I[3] = {&F,&G,&dihEqn};
			cellOption opt;
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,3,opt);
			}

			}
			break;


		// Section  VI.A.3.1
		case 572068135:
			{
			interval tx("6.3001");
			interval x[6]={"5.29","4","4","4","4","4"};
			interval z[6]={tx,tx,tx,tx,tx,tx};
			taylorFunction F = taylorQrtet::gamma
				+taylorQrtet::sol*(-zetapt)
				+taylorQrtet::dih*"0.2529"
				+taylorSimplex::unit*"-0.3442";
			taylorFunction G = taylorQrtet::dih
				+taylorSimplex::unit*"-1.51";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }	
			cout << "gamma done\n";
			taylorFunction H = 
              taylorQrtet::rad2 + taylorSimplex::unit*"-2";
			taylorFunction FV = taylorQrtet::vor
				+taylorQrtet::sol*(-zetapt)
				+taylorQrtet::dih*"0.2529"
				+taylorSimplex::unit*"-0.3442";
			t = generic3(domain::lowerD(x),domain::upperD(z),FV,G,H);
			}
			break;

		case 723700608:
			{
			interval tx("6.3001");
			interval x[6]={"5.29","4","4","4","4","8"};
			interval z[6]={tx,tx,tx,tx,tx,"9.1204"};//3.02^2
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::dih*"0.2529"
				+taylorSimplex::unit*"-0.1787";
			taylorFunction G = taylorSimplex::dih
				+taylorSimplex::unit*"-1.26";
			taylorFunction H = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"1.63";
			t= generic3(domain::lowerD(x),domain::upperD(z),F,G,H);
			}
			break;

		case 560470084:
			{
			interval tx("6.3001");
			interval x[6]={"4","5.29","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};

			/*gamma*/{
			taylorFunction F = taylorFlat::gamma
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih2*"0.2529"
				+taylorSimplex::unit*"-0.2137";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }	
			cout << "gamma done\n";
			}

			/*vor*/{
			taylorFunction FV = taylorFlat::vor
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih2*"0.2529"
				+taylorSimplex::unit*"-0.2137";
			taylorFunction H = 
              taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),FV,H))
				{ t = 0; break; }	
			cout << "vor done\n";
			}
			taylorFunction FVc = taylorSimplex::lowVorVc
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih2*"0.2529"
				+taylorSimplex::unit*"-0.2137";

			/*vorVc*/{
			interval xA[6]={"4.84","5.29","4","6.76","4","4"};
			if (!prove::generic(domain::lowerD(xA),domain::upperD(z),FVc))
				{ t = 0; break; }	
			cout << "vorVc done\n";
			}

			/*vorVc*/{
			interval xA[6]={"4","5.29","4","7.29","4","4"};
			if (!prove::generic(domain::lowerD(xA),domain::upperD(z),FVc))
				{ t = 0; break; }	
			cout << "vorVc done\n";
			}

			/*vorVc*/{
			taylorFunction G = 
              taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			t=generic2(domain::lowerD(x),domain::upperD(z),FVc,G);
			}

			}

			break;

		case 535502975:
			{
			interval tx("6.3001");
			interval x[6]={"5.29","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"9.1204","9.1204"};//3.02^2
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::dih*"0.2529"
				+taylorSimplex::unit*"-0.1371";
			taylorFunction G = taylorSimplex::dih
				+taylorSimplex::unit*"-1.14";
			taylorFunction H = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"1.51";
			t= generic3(domain::lowerD(x),domain::upperD(z),F,G,H);
			}
			break;

		// Section A.4.5.7

		case 424186517+1:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={"4.4944",tx,tx,"10.24",tx,tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.033";
			taylorFunction G = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"1.8";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 424186517+2:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","8","4","4"};
			interval z[6]={"7.268416",tx,tx,"10.24",tx,tx};
			taylorFunction F = taylorSimplex::highVorVc
				+taylorSimplex::unit*"0.058";
			taylorFunction G = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"2.5";
			cellOption opt;
			opt.setDihMax(2.5001);
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&F,&G};
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,2,opt);
			}
			break;

		case 424186517+3:
			{
			cout << "424186517+3" << "completed by Sam. F. " << endl;
			break;
			interval tx("6.3001");
			interval x[6]={tx,"4","4","8","4","4"};
			interval z[6]={"7.268416",tx,tx,"10.24",tx,tx};
			taylorFunction F = taylorSimplex::highVorVc
				+taylorSimplex::unit*"0.073";
			taylorFunction G = taylorSimplex::eta2_126
				+taylorSimplex::unit*"-2";
			cellOption opt;
			opt.setBigFace126();
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&F,&G};
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,2,opt);
			}
			break;

	// Section("VI.A.4.7.1");

		case 131574415:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={"4.84",tx,tx,tx*interval("4"),tx,tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-1.01"
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.05"
				+taylorSimplex::y3*"0.05"
				+taylorSimplex::y5*"0.15"
				+taylorSimplex::y6*"0.15";
			taylorFunction G = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"1.9";
			cellOption opt;
			opt.setDihMax(1.9001);
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[2] = {&F,&G};
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,2,opt);
			}
			break;

		case 929773933:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8",tx,"4"};
			interval z[6]={tx,tx,tx,tx*interval("4"),"8",tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-1.1227"
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.1"
				+taylorSimplex::y3*"0.03"
				+taylorSimplex::y5*"0.17"
				+taylorSimplex::y6*"0.16";
			taylorFunction G = taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"2.0";
			taylorFunction H = taylorSimplex::unit*"4.67"
				+taylorSimplex::y2*"-1"
				+taylorSimplex::y3*"-1";
			cellOption opt;
			opt.setDihMax(2.0);
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[3] = {&F,&G,&H};
			t=prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,3,opt);
			}
			break;

		case 223261160:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={"4.3264",tx,tx,"9",tx,tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-1.0159"
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.08"
				+taylorSimplex::y3*"0.08"
				+taylorSimplex::y4*"-0.04"
				+taylorSimplex::y5*"0.15"
				+taylorSimplex::y6*"0.15";
			t=prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 135018647:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8",tx,"4"};
			interval z[6]={tx,tx,tx,"9","8",tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-1.01054"
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.06"
				+taylorSimplex::y3*"0.06"
				+taylorSimplex::y4*"0.04"
				+taylorSimplex::y5*"0.12"
				+taylorSimplex::y6*"0.12";
			t=prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 559676877:
			{
			interval tx("6.3001");
			interval xA[6]={"4","4","4","8","4","4"};
			interval zA[6]={"4",tx,tx,"13.47",tx,tx};
			// x^2<13.47, where Delta[2.51,2.51,x,2sq,2.51,x]==0,
			interval xB[6]={"4","4","4","8",tx,"4"};
			interval zB[6]={"4",tx,tx,"13.47","8",tx};
			taylorFunction FA =
				taylorSimplex::lowVorVc
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::y5*"-0.0238"
				+taylorSimplex::y6*"-0.0238"
				+taylorSimplex::unit*"-0.4542";
			FA.setReducibleState(1); 
			taylorFunction FB =
				taylorSimplex::lowVorVc
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::y6*"-0.0238";
			FB.setReducibleState(1);
			const taylorFunction* IA[1] = {&FA};
			const taylorFunction* IB[1] = {&FB};
			cellOption opt;
			prove::recursiveVerifierQ(0,domain::lowerD(xA),domain::lowerD(xB),
				domain::upperD(zA),domain::upperD(zB),IA,IB,1,opt);
			t=1;
			}
			break;

		// Sectio VI.A.3.9.
		case 161665083:
			{
			interval tx("6.3001");
			// monotonicity arguments give y5=y6=2.51;
			interval x[6]={tx,"4","4","10.24",tx,tx};
			interval z[6]={"8",tx,tx,"10.24",tx,tx};
			taylorFunction F = taylorUpright::dih*"-1"
				+taylorSimplex::unit*"1.78";
			taylorFunction G = taylorSimplex::y2*"-1"
				+taylorSimplex::y3*"-1"
				+taylorSimplex::unit*"4.6";
			t=generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		// Section("VI.A.4.4.1");
		case 867513567:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};

			if (0) {
			taylorFunction F= taylorFlat::dih2
				+taylorSimplex::y1*"0.15"
				+taylorSimplex::y2*"-0.35"
				+taylorSimplex::y3*"0.15"
				+taylorSimplex::y4*"-0.7022"
				+taylorSimplex::y5*"0.17"
				+taylorSimplex::unit*"-0.0123";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-a done " << endl;
			}

			if (0) {
			taylorFunction F= taylorFlat::dih2*"-1"
				+taylorSimplex::y1*"-0.631"
				+taylorSimplex::y2*"0.13"
				+taylorSimplex::y3*"-0.31"
				+taylorSimplex::y4*"-0.413"
				+taylorSimplex::y5*"0.58"
				+taylorSimplex::y6*"-0.25"
				+taylorSimplex::unit*"2.63363";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-b done " << endl;
			}

			if (0) {
			taylorFunction F= taylorFlat::dih
				+taylorSimplex::y1*"-0.714"
				+taylorSimplex::y2*"0.221"
				+taylorSimplex::y3*"0.221"
				+taylorSimplex::y4*"-0.92"
				+taylorSimplex::y5*"0.221"
				+taylorSimplex::y6*"0.221"
				+taylorSimplex::unit*"0.3482";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-a done " << endl;
			}

			if (0) {
			taylorFunction F= taylorFlat::dih*"-1"
				+taylorSimplex::y1*"0.315"
				+taylorSimplex::y2*"-0.3972"
				+taylorSimplex::y3*"-0.3972"
				+taylorSimplex::y4*"0.715"
				+taylorSimplex::y5*"-0.3972"
				+taylorSimplex::y6*"-0.3972"
				+taylorSimplex::unit*"2.37097";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-b done " << endl;
			}

			if (0) {
			taylorFunction F= taylorSimplex::unit*"-1.17401"
				+taylorSimplex::y1*"0.145"
				+taylorSimplex::y2*"0.081"
				+taylorSimplex::y3*"0.081"
				//+taylorSimplex::y4*"0.715"
				+taylorSimplex::y5*"0.133"
				+taylorSimplex::y6*"0.133";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-a done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"-0.94903"
				+taylorSimplex::y1*"0.12"
				+taylorSimplex::y2*"0.081"
				+taylorSimplex::y3*"0.081"
				+taylorSimplex::y4*"-0.029"
				+taylorSimplex::y5*"0.113"
				+taylorSimplex::y6*"0.113";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-b done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"-1.05382"
				+taylorSimplex::y4*"0.153"
				+taylorSimplex::y5*"0.153"
				+taylorSimplex::y6*"0.153";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-c done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"-1.449"
				+taylorFlat::sol*"0.419351"
				+taylorSimplex::y1*"0.19"
				+taylorSimplex::y2*"0.19"
				+taylorSimplex::y3*"0.19";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-d done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"0.01465"
				+taylorFlat::sol*"0.419351"
				+taylorFlat::dih*"-0.079431"
				+taylorSimplex::y5*"-0.0436"
				+taylorSimplex::y6*"-0.0436";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-d done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"-0.0114";
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " sig-e done " << endl;
			}

			{
			interval pt("0.05537364566846386973");
			taylorFunction F= taylorSimplex::unit*
				(pt*interval("1.019"))
				+taylorFlat::sol*(-zetapt);
			if (!genericFlatSigma(F)) { t = 0; break; }
			cout << " tau-a done " << endl;
			}

			t=1;
			}
			break;

		//Section("VI.A.4.5.1");
		case 498839271:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};

			{
			taylorFunction F= taylorUpright::dih*"-1"
				+taylorSimplex::y1*"0.636"
				+taylorSimplex::y2*"-0.462"
				+taylorSimplex::y3*"-0.462"
				+taylorSimplex::y4*"0.82"
				+taylorSimplex::y5*"-0.462"
				+taylorSimplex::y6*"-0.462"
				+taylorSimplex::unit*"1.82419";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-a done " << endl;
			}

			{
			taylorFunction F= taylorUpright::dih
				+taylorSimplex::y1*"-0.55"
				+taylorSimplex::y2*"0.214"
				+taylorSimplex::y3*"0.214"
				+taylorSimplex::y4*"-1.24"
				+taylorSimplex::y5*"0.214"
				+taylorSimplex::y6*"0.214"
				+taylorSimplex::unit*"0.75281";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-b done " << endl;
			}

			{
			taylorFunction F= taylorUpright::dih2*"-1"
				+taylorSimplex::y1*"-0.4"
				+taylorSimplex::y2*"0.15"
				+taylorSimplex::y3*"-0.09"
				+taylorSimplex::y4*"-0.631"
				+taylorSimplex::y5*"0.57"
				+taylorSimplex::y6*"-0.23"
				+taylorSimplex::unit*"2.5481";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-a done " << endl;
			}

			{
			taylorFunction F= taylorUpright::dih2
				+taylorSimplex::y1*"0.454"
				+taylorSimplex::y2*"-0.34"
				+taylorSimplex::y3*"-0.154"
				+taylorSimplex::y4*"0.346"
				+taylorSimplex::y5*"-0.805"
				+taylorSimplex::unit*"-0.3429";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-b done " << endl;
			}

			{
			taylorFunction F= taylorUpright::sol*"-1"
				+taylorSimplex::y2*"-0.065"
				+taylorSimplex::y3*"-0.065"
				+taylorSimplex::y4*"-0.061"
				+taylorSimplex::y5*"0.115"
				+taylorSimplex::y6*"0.115"
				+taylorSimplex::unit*"0.2618";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " sol-a done " << endl;
			}

			{
			taylorFunction F= taylorUpright::sol
				+taylorSimplex::y1*"0.293"
				+taylorSimplex::y2*"0.03"
				+taylorSimplex::y3*"0.03"
				+taylorSimplex::y4*"-0.12"
				+taylorSimplex::y5*"-0.325"
				+taylorSimplex::y6*"-0.325"
				+taylorSimplex::unit*"0.2514";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " sol-b done " << endl;
			}

			{
			taylorFunction F= gammaNu
				+taylorSimplex::y2*"0.0538"
				+taylorSimplex::y3*"0.0538"
				+taylorSimplex::y4*"-0.083"
				+taylorSimplex::y5*"0.0538"
				+taylorSimplex::y6*"0.0538"
				+taylorSimplex::unit*"-0.5995";;
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-a done " << endl;
			}

			{
			taylorFunction F= vorNu
				+taylorSimplex::y2*"0.0538"
				+taylorSimplex::y3*"0.0538"
				+taylorSimplex::y4*"-0.083"
				+taylorSimplex::y5*"0.0538"
				+taylorSimplex::y6*"0.0538"
				+taylorSimplex::unit*"-0.5995";;
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-a done " << endl;
			}

			{
			interval pt("0.05537364566846386973");
			taylorFunction F= gammaNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*(interval("0.5945")*pt);
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " tau-a done " << endl;
			}

			{
			interval pt("0.05537364566846386973");
			taylorFunction F= vorNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*(interval("0.5945")*pt);
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " tauV-a done " << endl;
			}
			t=1;
			}
			break;

		// Section("VI.A.4.5.4");
		case 319046543:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"7.268416",tx,tx,tx,tx,tx};

			if (0) {
			taylorFunction F= taylorUpright::dih*"-1"
				+taylorSimplex::y1*"0.49"
				+taylorSimplex::y2*"-0.44"
				+taylorSimplex::y3*"-0.44"
				+taylorSimplex::y4*"0.82"
				+taylorSimplex::y5*"-0.44"
				+taylorSimplex::y6*"-0.44"
				+taylorSimplex::unit*"2.0421";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-a done " << endl;
			}

			if (0) {
			taylorFunction F= taylorUpright::dih
				+taylorSimplex::y1*"-0.495"
				+taylorSimplex::y2*"0.214"
				+taylorSimplex::y3*"0.214"
				+taylorSimplex::y4*"-1.05"
				+taylorSimplex::y5*"0.214"
				+taylorSimplex::y6*"0.214"
				+taylorSimplex::unit*"0.2282";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih1-b done " << endl;
			}

			if (0) {
			taylorFunction F= taylorUpright::dih2*"-1"
				+taylorSimplex::y1*"-0.38"
				+taylorSimplex::y2*"0.15"
				+taylorSimplex::y3*"-0.09"
				+taylorSimplex::y4*"-0.54"
				+taylorSimplex::y5*"0.57"
				+taylorSimplex::y6*"-0.24"
				+taylorSimplex::unit*"2.3398";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-a done " << endl;
			}

			if (0) {
			taylorFunction F= taylorUpright::dih2
				+taylorSimplex::y1*"0.375"
				+taylorSimplex::y2*"-0.33"
				+taylorSimplex::y3*"-0.11"
				+taylorSimplex::y4*"0.36"
				+taylorSimplex::y5*"-0.72"
				+taylorSimplex::y6*"-0.034"
				+taylorSimplex::unit*"-0.36135";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih2-b done " << endl;
			}

			if (0) {
			taylorFunction F= taylorUpright::sol*"-1"
				+taylorSimplex::y1*"-0.42"
				+taylorSimplex::y2*"-0.165"
				+taylorSimplex::y3*"-0.165"
				+taylorSimplex::y4*"0.06"
				+taylorSimplex::y5*"0.135"
				+taylorSimplex::y6*"0.135"
				+taylorSimplex::unit*"1.479";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " sol-a done " << endl;
			}

			if (0) {
			taylorFunction F= taylorUpright::sol
				+taylorSimplex::y1*"0.265"
				+taylorSimplex::y2*"0.06"
				+taylorSimplex::y3*"0.06"
				+taylorSimplex::y4*"-1.24"
				+taylorSimplex::y5*"-0.296"
				+taylorSimplex::y6*"-0.296"
				+taylorSimplex::unit*"0.0997";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " sol-b done " << endl;
			}

			if (0) {
			taylorFunction F= gammaNu
				+taylorSimplex::y1*"-0.112"
				+taylorSimplex::y2*"0.142"
				+taylorSimplex::y3*"0.142"
				+taylorSimplex::y4*"0.16"
				+taylorSimplex::y5*"0.074"
				+taylorSimplex::y6*"0.074"
				+taylorSimplex::unit*"-0.9029";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-a done " << endl;
			}

			if (0) {
			taylorFunction F= vorNu
				+taylorSimplex::y1*"-0.112"
				+taylorSimplex::y2*"0.142"
				+taylorSimplex::y3*"0.142"
				+taylorSimplex::y4*"0.16"
				+taylorSimplex::y5*"0.074"
				+taylorSimplex::y6*"0.074"
				+taylorSimplex::unit*"-0.9029";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-a done " << endl;
			}

			if (0) {
			taylorFunction F= gammaNu
				+taylorUpright::dih*"0.07611"
				+taylorSimplex::unit*"-0.11";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-b done " << endl;
			}

			if (0) {
			taylorFunction F= vorNu
				+taylorUpright::dih*"0.07611"
				+taylorSimplex::unit*"-0.11";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-b done " << endl;
			}

			if (0) {
			taylorFunction F= gammaNu
				+taylorSimplex::y1*"0.015"
				+taylorSimplex::y2*"0.16"
				+taylorSimplex::y3*"0.16"
				+taylorSimplex::y4*"0.16"
				+taylorSimplex::y5*"0.0738"
				+taylorSimplex::y6*"0.0738"
				+taylorSimplex::unit*"-1.29285";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-c done " << endl;
			}

			if (0){
			taylorFunction F= gammaNu
				+taylorUpright::sol*(-zetapt)
				+taylorUpright::dih*"0.07106"
				+taylorSimplex::unit*"-0.06429";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-d done " << endl;
			}

			if(0){
			taylorFunction F= vorNu
				+taylorUpright::sol*(-zetapt)
				+taylorUpright::dih*"0.07611"
				+taylorSimplex::unit*"-0.06429";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-d done " << endl;
			}

			if(0){
			taylorFunction F= gammaNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*"0.0414";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-e done " << endl;
			}

			if (0){
			taylorFunction F= vorNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*"0.0414";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-e done " << endl;
			}

			if (0)/* patch-1 */{
			interval zA[6]={"7.268416",tx,tx,"6.125625",tx,tx};
			taylorFunction F= taylorUpright::dih
				+taylorSimplex::y1*"-0.495"
				+taylorSimplex::y2*"0.214"
				+taylorSimplex::y3*"0.214"
				+taylorSimplex::y4*"-1.05"
				+taylorSimplex::y5*"0.214"
				+taylorSimplex::y6*"0.214"
				+taylorSimplex::unit*"0.23545";
			if (!prove::generic(domain::lowerD(x),domain::upperD(zA),F))
				{ t = 0; break; }
			cout << " dih1-patch1 done " << endl;
			} 

			if (0)/* patch-2 */{
			interval xA[6]={tx,"4","4","6.125625","4","4"};
			interval zA[6]={"7.1824",tx,tx,tx,tx,tx};
			taylorFunction F= taylorUpright::dih
				+taylorSimplex::y1*"-0.495"
				+taylorSimplex::y2*"0.214"
				+taylorSimplex::y3*"0.214"
				+taylorSimplex::y4*"-1.05"
				+taylorSimplex::y5*"0.214"
				+taylorSimplex::y6*"0.214"
				+taylorSimplex::unit*"0.23545";
			if (!prove::generic(domain::lowerD(xA),domain::upperD(zA),F))
				{ t = 0; break; }
			cout << " dih1-patch2 done " << endl;
			} 

			/* patch-3-gamma */{
			interval xA[6]={"7.1824","4","4","6.125625","4","4"};
			interval zA[6]={"7.268416",tx,tx,tx,tx,tx};
			taylorFunction F= gammaNu
				+taylorSimplex::highVorVc*"-1"
				+taylorSimplex::unit*"0.03122";
			if (!prove::generic(domain::lowerD(xA),domain::upperD(zA),F))
				{ t = 0; break; }
			cout << " dih1-patch3-gamma done " << endl;
			} 

			/* patch-3-vor */{
			interval xA[6]={"7.1824","4","4","6.125625","4","4"};
			interval zA[6]={"7.268416",tx,tx,tx,tx,tx};
			taylorFunction F= vorNu
				+taylorSimplex::highVorVc*"-1"
				+taylorSimplex::unit*"0.03122";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(xA),domain::upperD(zA),F,G))
				{ t = 0; break; }
			cout << " dih1-patch3-vor done " << endl;
			} 

			t=1;
			}
			break; 

		case 533270809:
			/* patch-4-gamma */{
			interval tx("6.3001");
			interval xA[6]={"7.1824","4","4","4","4","4"};
			interval zA[6]={"7.268416",tx,tx,tx,tx,tx};
			taylorFunction F= gammaNu
				+taylorSimplex::highVorVc*"-1"
				+taylorSimplex::unit*"-0.007805";
			if (!prove::generic(domain::lowerD(xA),domain::upperD(zA),F))
				{ t = 0; break; }
			cout << " patch4-gamma done " << endl;
			} 

		// Section("VI.A.4.5.5");
		case 365179082:

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4",tx,"4","4"};
			interval z[6]={"7.268416",tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::highVorVc
				+taylorSimplex::unit*"0.05";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vor-a done " << endl;
			}

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4",tx,"4","4"};
			interval z[6]={"7.268416",tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::unit*"0.119";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-b done " << endl;
			}

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","7.6729","4","4"};
			interval z[6]={"7.268416",tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::highVorVc
				+taylorSimplex::unit*"0.119";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-c done " << endl;
			}
			t=1; break;


		//Section("VI.A.4.9.1");

		case 529738375:
			{
			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.6729","7.6729"};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.105"
				+taylorSimplex::y3*"0.105"
				+taylorSimplex::y4*"0.115"
				+taylorSimplex::y5*"0.062"
				+taylorSimplex::y6*"0.062"
				+taylorSimplex::unit*"-1.02014";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vor done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.6729","7.6729"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.105"
				+taylorSimplex::y3*"0.105"
				+taylorSimplex::y4*"0.115"
				+taylorSimplex::y5*"0.062"
				+taylorSimplex::y6*"0.062"
				+taylorSimplex::unit*"-1.02014";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vorVc done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,"7.6729"};
			interval z[6]={tx,tx,tx,tx,"7.6729","8"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.105"
				+taylorSimplex::y3*"0.105"
				+taylorSimplex::y4*"0.115"
				+taylorSimplex::y5*"0.062"
				+taylorSimplex::y6*"0.062"
				+taylorSimplex::unit*"-1.02014";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vorVc' done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.6729","7.6729"};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::unit*"-0.3085";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vor done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.6729","7.6729"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::unit*"-0.3085";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vorVc done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,"7.6729"};
			interval z[6]={tx,tx,tx,tx,"7.6729","8"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::unit*"-0.3085";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vorVc' done " << endl;
			}

			if (0) {
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,tx,tx};
			interval z[6]={tx,tx,tx,"8","8","8"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.121";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " vorVc'' done " << endl;
			}

			if (1) {
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,tx,tx};
			interval z[6]={tx,tx,tx,"8","8","8"};
			taylorFunction F= taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"2.17382"
				+taylorSimplex::y1*"0.115"
				+taylorSimplex::y2*"-0.452"
				+taylorSimplex::y3*"-0.452"
				+taylorSimplex::y4*"0.618"
				+taylorSimplex::y5*"-0.15"
				+taylorSimplex::y6*"-0.15";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << " dih (2.17382)'' done " << endl;
			}

			if (1) {
			interval tx("6.3001");
			interval x[6]={tx,"4","4",tx,"4","4"};
			interval z[6]={"8",tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"2.82998"
				+taylorSimplex::y1*"0.47"
				+taylorSimplex::y2*"-0.522"
				+taylorSimplex::y3*"-0.522"
				+taylorSimplex::y4*"0.812"
				+taylorSimplex::y5*"-0.522"
				+taylorSimplex::y6*"-0.522";
			cellOption opt;
			opt.setDihMax(2.4);
			// Plug in extreme valuesfor yi and 2.4 for dihmax , then true.
			domain x0 = domain::lowerD(x),z0 = domain::upperD(z);
			const taylorFunction* I[1] = {&F};
			if (!prove::recursiveVerifier(0,domain::lowerD(x),
									domain::upperD(z),x0,z0,I,1,opt))
				{ t = 0; break; }
			cout << " dih (4.9.2, 2.82998)'' done " << endl;
			}

			t = 1; break;
			}

		// Section("VI.A.4.12");
		case 704795925:
			{
			interval tx("6.3001");
			interval x[6]={"7.268416","6.0025","4","4","4","6.0025"};
			interval z[6]={"8",tx,tx,tx,tx,tx};

			{
			taylorFunction F= gammaNu
				+taylorSimplex::unit*"0.055";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " gamma-a done " << endl;
			}

			{
			taylorFunction F= vorNu
				+taylorSimplex::unit*"0.055";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " vor-a done " << endl;
			}

			{
			taylorFunction F= gammaNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*"0.092";
			taylorFunction G = 
				taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
				taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }
			cout << " tau-a done " << endl;
			}

			{
			taylorFunction F= vorNu
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*"0.092";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{ t = 0; break; }
			cout << " tauV-a done " << endl;
			}

			t=1; break;
			}

		case 332919646:

			{
			interval tx("6.3001");
			interval x[6]={"4","6.0025","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			{
			taylorFunction F= taylorSimplex::unit*"0.039";
			if (!genericFlatSigmaX(F,x,z)) { t = 0; break; }
			cout << " sighat done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::unit*"0.094"
				+taylorFlat::sol*(-zetapt);
			if (!genericFlatSigmaX(F,x,z)) { t = 0; break; }
			cout << " tauhat done " << endl;
			}
			t=1; break;
			}

		case 335795137:

			{
			interval tx("6.3001");
			interval x[6]={"7.268416","6.0025","4",tx,"4","6.0025"};
			interval z[6]={"8",tx,tx,"8",tx,tx};

			{
			taylorFunction F= taylorSimplex::vor
					+taylorSimplex::unit*"0.197";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F)) 
				{ t = 0; break; }
			cout << " vor done " << endl;
			}

			{
			taylorFunction F= taylorSimplex::vor
					+taylorSimplex::sol*(-zetapt)
					+taylorSimplex::unit*"0.239";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				 { t = 0; break; }
			cout << " tauV done " << endl;
			}

			t=1; break;
			}

		// Section("VI.A.7");
		case 104506452:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"7.268416",tx,tx,tx,tx,tx};
			taylorFunction octavorVc = (taylorUpright::swapVorVc+
				taylorUpright::vorVc)*"0.5";
			taylorFunction F= taylorUpright::octavor
					+octavorVc*"-1"
				+taylorSimplex::unit*"0.008";
			taylorFunction G = 
				taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 601083647:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","9","4","4"};
			interval z[6]={tx,tx,tx,"9",tx,tx};
			taylorFunction F= taylorSimplex::dih*"-1"
				+taylorSimplex::unit*"-1.678";
			taylorFunction G = taylorSimplex::unit*"8.77"
				+taylorSimplex::y2*"-1"
				+taylorSimplex::y3*"-1"
				+taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 543730647:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"6.76","4.57104",tx}; 
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y5*"0.157"
				+taylorSimplex::unit*"-0.3138";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 163030624:
			{
			interval tx("6.3001");
			interval x[6]={"4","4.498641","4",tx,"4.9284","4"};
			interval z[6]={tx,tx,tx,"6.76","5.008644",tx}; 
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::unit*"0.06";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 181462710:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={"4.84","4.84","4.84","8","5.5225","5.5225"}; 
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::unit*"-1.4"
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.15"
				+taylorSimplex::y3*"0.15"
				+taylorSimplex::y5*"0.15"
				+taylorSimplex::y6*"0.15";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;


		// Section("VI.A2");
		case 480930831:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"7.6729","4"};
			interval z[6]={tx,tx,tx,"8","8",tx};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::unit*"0.077";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 463544803:

			{
			interval tx("6.3001");
			interval tz("4.5796");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tz,tz,tz,"8",tx,tx};
			taylorFunction F= taylorFlat::vor
				+taylorSimplex::lowVorVc*"-1";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 594246986:

			{
			interval tx("6.3001");
			interval tz("4.5796");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tz,tz,tz,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.145"
				+taylorSimplex::y2*"0.08"
				+taylorSimplex::y3*"0.08"
				+taylorSimplex::y5*"0.133"
				+taylorSimplex::y6*"0.133"
				+taylorSimplex::unit*"-1.146";
			taylorFunction G = 
				taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 381970727:

			{
			interval tx("6.3001");
			interval tz("4.5796");
			interval tw("5.29");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tz,tz,tz,"8",tw,tw};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.145"
				+taylorSimplex::y2*"0.081"
				+taylorSimplex::y3*"0.081"
				+taylorSimplex::y5*"0.16"
				+taylorSimplex::y6*"0.16"
				+taylorSimplex::unit*"-1.255";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 951798877:

			{
			interval tx("6.3001");
			interval tz("4.5796");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tz,tz,tz,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.03"
				+taylorSimplex::y2*"0.03"
				+taylorSimplex::y3*"0.03"
				+taylorSimplex::y5*"0.094"
				+taylorSimplex::y6*"0.094"
				+taylorSimplex::unit*"-0.5361";
			taylorFunction G =
				taylorSimplex::y5
				+taylorSimplex::y6
				+taylorSimplex::unit*"-4.3";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 923397705:

			{
			interval tx("6.3001");
			interval tz("4.5796");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tz,tz,tz,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.03"
				+taylorSimplex::y2*"0.03"
				+taylorSimplex::y3*"0.03"
				+taylorSimplex::y5*"0.16"
				+taylorSimplex::y6*"0.16"
				+taylorSimplex::unit*"-0.82"
				+taylorSimplex::unit*"-1.0e-6";
			taylorFunction G =
				taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1"
				+taylorSimplex::unit*"4.3";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 495568072:

			{
			interval tx("6.3001");
			interval tz("4");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tz,tz,tz,"7.29",tx,tx};
			taylorFunction F= 
				taylorSimplex::y4*"-1.69"
				+taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1"
				+taylorSimplex::unit*"9.0659";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 378020227:

			{
			interval tx("6.3001");
			interval tz("4.5796"); // 2.14^2
			interval tu("7.6729");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tz,tz,tz,tx,tu,tu};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.08"
				+taylorSimplex::y3*"0.08"
				+taylorSimplex::y4*"0.16"
				+taylorSimplex::y5*"0.21"
				+taylorSimplex::y6*"0.21"
				+taylorSimplex::unit*"-1.7531";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 256893386:

			{
			interval tx("6.3001");
			interval tz("4.5796"); // 2.14^2
			interval tu("7.6729");
			interval x[6]={"4","4","4","4",tx,tu};
			interval z[6]={tz,tz,tz,tx,"8","8"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.1"
				+taylorSimplex::y3*"0.1"
				+taylorSimplex::y4*"0.165"
				+taylorSimplex::y5*"0.115"
				+taylorSimplex::y6*"0.115"
				+taylorSimplex::unit*"-1.38875";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 749955642:

			{
			interval tx("6.3001");
			interval tz("4");
			interval tu("7.6729");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tz,tz,tz,tx,tu,tu}; 
			taylorFunction F= 
				taylorSimplex::y4*"-1"
				+taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1"
				+taylorSimplex::unit*"7.206";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 653849975:

			{
			interval tx("6.3001");
			interval tz("4.5796"); // 2.14^2
			interval tu("7.6729");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tz,tz,tz,tx,tu,tu};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::y1*"0.058"
				+taylorSimplex::y2*"0.05"
				+taylorSimplex::y3*"0.05"
				+taylorSimplex::y4*"0.16"
				+taylorSimplex::y5*"0.13"
				+taylorSimplex::y6*"0.13"
				+taylorSimplex::unit*"-1.24547";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;
		


		

	// Section("VI.A2.etc.");
	 case 312481617:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"5.5225","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::unit*"0.053";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 292760488:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"5.0625","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::unit*"0.041";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 399326202:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"7.3984",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.064";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 794413343:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","7.3984","4","4"};
			interval z[6]={"4","4","4","7.3984",tx,tx};
			taylorFunction F= taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1"
				+taylorSimplex::unit*"4.4";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 569240360:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-1.0612"
				+taylorSimplex::y1*"0.08"
				+taylorSimplex::y2*"0.08"
				+taylorSimplex::y3*"0.08"
				+taylorSimplex::y5*"0.142"
				+taylorSimplex::y6*"0.142";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 271703736:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.6729","7.6729"};
			taylorFunction F= taylorSimplex::vor
			+taylorSimplex::sol*"0.419351"
				+taylorSimplex::unit*"-0.289";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 155008179:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::sol*"0.419351"
				+taylorSimplex::dih*"-0.079431"
				+taylorSimplex::y5*"-0.0436"
				+taylorSimplex::y6*"-0.0436"
				+taylorSimplex::unit*"0.0294";
			taylorFunction G = taylorSimplex::eta2_456*"-1"
				+taylorSimplex::unit*"2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;
 
	 case 819450002:

			{
			interval tx("6.3001");
			interval tu("4.5369");
			interval x[6]={"4","4","4",tx,"4","5.1529"};
			interval z[6]={tu,tu,tu,"7.1289","4.41","5.9049"};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.1"
				+taylorSimplex::y3*"0.1"
				+taylorSimplex::y5*"0.17"
				+taylorSimplex::y6*"0.11"
				+taylorSimplex::unit*"-1.1457";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 252231882:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","6.7081","6.1009","4.41"};
			interval z[6]={tx,tx,tx,"6.9696",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.0713";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 900212351:

			{
			interval tx("6.3001");
			interval tu("4.5369");
			interval x[6]={"4","4","4","4","7.29","7.29"};
			interval z[6]={tu,tu,tu,tx,"7.6729","7.6729"};
			taylorFunction F= taylorFlat::gamma
				+taylorSimplex::y1*"0.1"
				+taylorSimplex::y2*"0.1"
				+taylorSimplex::y3*"0.1"
				+taylorSimplex::y5*"0.17"
				+taylorSimplex::y6*"0.17"
				+taylorSimplex::unit*"-1.798";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 472436181:

			{
			interval tx("6.3001");
			interval tu("4.5369");
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tu,tu,tu,"7.5076",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.06";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 913534858:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"7.546009",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.058";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 850226792:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"7.6729",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.0498";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	 case 455329491:

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4",tx,"4","4"};
			interval z[6]={"8",tx,tx,"7.26895521",tx,tx};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::unit*"0.039";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	 case 857241493:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4",tx,tx};
			interval z[6]={tx,tx,tx,tx,"7.26895521","7.26895521"};
			taylorFunction F= taylorSimplex::vorSqc
				+taylorSimplex::unit*"0.078";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	// Section("VI. stray ineqs.");
	case 838887715:

			{
			interval tx("6.3001");
			interval tz("4");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tz,tz,tz,"7.6729",tx,tx};
			taylorFunction F= 
				taylorSimplex::y4*"-1.69"
				+taylorSimplex::y5*"-1"
				+taylorSimplex::y6*"-1"
				+taylorSimplex::unit*"9.044";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			t= generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

	case 292827481:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8",tx};
			interval z[6]={"4",tx,"4","4","10.24",tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.311979797464466613664"
				+taylorSimplex::y5*"0.1";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 710875528:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","4"};
			interval z[6]={"4","4","4","4","10.24","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.009"
				+taylorSimplex::unit*"0.282842712474619009760"
				+taylorSimplex::y5*"-0.1";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 354217730:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","10.24"};
			interval z[6]={tx,tx,tx,"4","10.24","12.0409"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.20597979746446661366"
				+taylorSimplex::y5*"0.14";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 595674181:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","10.24"};
			interval z[6]={tx,tx,tx,"4","10.24","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorUpright::sol*(-zetapt)
				+taylorSimplex::unit*"0.281";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 938003786:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","4"};
			interval z[6]={tx,tx,tx,"4","10.24","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.386979797464466613664"
				+taylorSimplex::y5*"-0.14";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	// Group 2 .
	case 912536613:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F = taylorFlat::gamma
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih*"-0.316"
				+taylorSimplex::unit*"0.5765";
			taylorFunction G = 
              taylorSimplex::eta2_456*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
              taylorFlat::dih*"-1"
			+taylorSimplex::unit*"1.55";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{ t = 0; break; }	
			cout << "gamma done\n";

			taylorFunction F2 = taylorFlat::vor
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih*"-0.316"
				+taylorSimplex::unit*"0.5765";
			taylorFunction G2 = 
              taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			if (!generic3(domain::lowerD(x),domain::upperD(z),F2,G2,H))
				{ t = 0; break; }	

			taylorFunction G3 = 
              taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			t=generic3(domain::lowerD(x),domain::upperD(z),F2,G3,H);
			}
			break;

	case 640248153:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={tx,tx,tx,"26",tx,tx};
			taylorFunction F = taylorSimplex::lowVorVc
				+taylorFlat::sol*(-zetapt)
				+taylorFlat::dih*"-0.316"
				+taylorSimplex::unit*"0.5765";
			taylorFunction H = 
              taylorFlat::dih*"-1"
			+taylorSimplex::unit*"1.55";
			t=generic2dih(domain::lowerD(x),domain::upperD(z),F,H,1.5500001);
			}

	case 594902677:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = gammaNu
				+taylorFlat::sol*(-zetapt)
				+taylorUpright::dih2*"-0.316"
				+taylorSimplex::unit*"0.2778";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }	
			cout << "gammaNu done\n";

			taylorFunction F2 = vorNu
				+taylorFlat::sol*(-zetapt)
				+taylorUpright::dih2*"-0.316"
				+taylorSimplex::unit*"0.2778";
			taylorFunction G = 
              taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }	

			taylorFunction G2 = 
              taylorSimplex::eta2_135 + taylorSimplex::unit*"-2";
			t = generic2(domain::lowerD(x),domain::upperD(z),F2,G2);

			}
			break;

	case 968721007:

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4",tx};
			interval z[6]={"8","4",tx,"4",tx,"7.5625"};
			taylorFunction F= taylorSimplex::highVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.159"
				+taylorSimplex::dih*"-0.0822";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 783968228:

			{
			interval tx("6.3001");
			interval x[6]={tx,tx,"4","4","4",tx};
			interval z[6]={"8",tx,tx,"4",tx,tx};
			taylorFunction F= taylorSimplex::dih
				+taylorSimplex::unit*"-1.23";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 745174731:

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","7.5625"};
			interval z[6]={"8","4",tx,"4",tx,"7.5625" };
			taylorFunction F= taylorSimplex::dih
				+taylorSimplex::unit*"-1.23";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	// Group 3.
	//case 986970370:
	//case 677910379:
	case 276168273:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","9.3636","9.3636"};
			interval z[6]={"4","4",tx,"4","10.4329","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"0.128";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 411203982:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","9.3636","9.3636"};
			interval z[6]={"4","4","4","4","10.4329","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.36925";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 860823724:

			{
			interval tx("6.3001");
			interval x[6]={"4","4",tx,"4","9.3636","9.3636"};
			interval z[6]={"4","4",tx,"4","10.4329","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.31";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 353116995:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","9.3636"};
			interval z[6]={"4",tx,tx,tx,"10.4329","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::y5*"0.14"
				+taylorSimplex::unit*"-0.39597979746446661"
				+taylorSimplex::unit*"0.137";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 943315982:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","9.641025"};
			interval z[6]={"4",tx,tx,tx,"10.4329","10.4329"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::y5*"0.14"
				+taylorSimplex::unit*"-0.39597979746446661"
				+taylorSimplex::unit*"0.31";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 941799628:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","9.3636"};
			interval z[6]={"4",tx,tx,tx,"10.4329","9.641025"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::y5*"0.14"
				+taylorSimplex::unit*"-0.39597979746446661"
				+taylorSimplex::y6*"0.19"
				+taylorSimplex::unit*"-0.58995"
				+taylorSimplex::unit*"0.31";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 674284283:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","4"};
			interval z[6]={"4","4",tx,"4","10.4329","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				//+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::y5*"-0.14"
				+taylorSimplex::unit*"0.39597979746446661"
				+taylorSimplex::unit*"-0.009";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 775220784:

			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","4","8","4"};
			interval z[6]={"4","4",tx,"4","10.4329","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::y5*"-0.14"
				+taylorSimplex::unit*"0.39597979746446661"
				+taylorSimplex::unit*"0.05925";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 286076305:

			{
			interval tx("6.3001");
			interval x[6]={"4","4",tx,"8","4","4"};
			interval z[6]={tx,tx,tx,"10.4329","4","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.05925";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

	case 589319960:

			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","9.3636","4","4"};
			interval z[6]={tx,"4","4","9.641025","4","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::y4*"-0.19"
				+taylorSimplex::unit*"0.58995";
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		default : t=0; error::message("missing case"); break;

		}
	//ZZ
	
	if (t) cout << "Verification complete" << endl;
	else cout << "FAIL! " << identifier << endl;
	error::printTime();
	}

void Section(char* s)
	{
	selfTest();
	cout << "\n\nSection " << s << endl << endl;
	}

int main()
	{
	/*
	Section("VI.A.2.5");
	verify(269048407);
	verify(553285469);

	verify(293389410);
	verify(695069283);
	verify(814398901);
	verify(352079526);
	verify(179025673);

	Section("VI.A.3.1");
	verify(572068135);
	verify(723700608);
	verify(560470084);
	verify(535502975);

	Section("VI.A.3.9");
	verify(161665083);

	Section("VI.A.4.4.1");
	verify(867513567); // restarted with if (0) on those already done.

	Section("VI.A.4.5.1");
	verify(498839271);

	Section("VI.A.4.5.4");
	verify(319046543); // restarted clearing various cases done to (0).
	verify(533270809);

	Section("VI.A.4.5.5");
	verify(365179082);

	Section("VI.A.4.5.7");
	verify(424186517+1);
	verify(424186517+2);
	verify(424186517+3);

	Section("VI.A.4.7.1");
	verify(131574415);
	verify(929773933);
	verify(223261160);
	verify(135018647);
	verify(559676877); 

	Section("VI.A.4.9.1");
	verify(529738375); // if (0) added on 2nd pass.

	Section("VI.A.4.12");
	verify(704795925);
	verify(332919646);
	verify(335795137);

	Section("VI.A.7");
	verify(104506452);
	verify(601083647);
	verify(543730647);
	verify(163030624);
	verify(181462710);

	Section("VI.A2");
	//verify(480930831);
	//verify(463544803);  // restart...
	verify(594246986);
	verify(381970727);
	verify(951798877);
	verify(923397705);
	verify(495568072);
	verify(378020227);
	verify(256893386);
	verify(749955642);
	verify(653849975);

	Section("VI.A2.etc.");
	verify(312481617);
	verify(292760488);
	verify(399326202);
	verify(794413343);
	verify(569240360);
	verify(271703736);
	verify(155008179);

	verify(819450002);
	verify(252231882);
	verify(900212351);
	verify(472436181);
 
	verify(913534858);
	verify(850226792);
	verify(455329491);
	verify(857241493);


	Section("VI. stray ineqs.");
	verify(838887715);
	verify(292827481);
	verify( 710875528);
	verify(354217730);
	verify(595674181);
	verify(938003786);
	
	Section("VI. stray ineqs.2");
	verify(912536613);
	verify(640248153);
	verify(594902677);
	*/
	verify(968721007);
	verify(783968228);
	verify(745174731);
/*
	Section("VI. stray ineqs.3");
	//verify(986970370);
	//verify(677910379);
	verify(276168273);
	verify(411203982);
	verify(860823724);
	verify(353116995);
	verify(943315982);
	verify(941799628);
	verify(674284283);
	verify(775220784);
	verify(286076305);
	verify(589319960);
	cout << "all done!" << endl;
	*/
	}
