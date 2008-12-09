#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"

// These were added 5/27/98. 

void selfTest()
    {
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    }


static void setqr(domain& x,domain& z)
	{
	interval tx[6]={"4","4","4","4","4","4"};
	interval tz[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	x = domain::lowerD(tx);
	z = domain::upperD(tz);
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


// a small variation of prove::qrtet/
int qrtet2(const domain& x,const domain& z,
	const taylorFunction& F,
	const taylorFunction& J)
    {
    /*gamma*/{
    domain x0=x,z0=z;
    interval s141("1.41"); s141 = s141*s141;
    taylorFunction G = F+taylorQrtet::gamma;
    taylorFunction H = taylorQrtet::rad2*"-1" + taylorSimplex::unit*s141;
    G.setReducibleState(F.getReducibleState());
    H.setReducibleState(1);
    const taylorFunction* I[3]= {&G,&J,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt)) return 0;
    }
    error::printTime("gamma done! ");
    /*vor*/{
    domain x0=x,z0=z;
    interval s141("1.41"); s141 = s141*s141;
    taylorFunction G = F+taylorQrtet::vor;
    taylorFunction H = taylorQrtet::rad2 + taylorSimplex::unit*(-s141);
    G.setReducibleState(F.getReducibleState());
    H.setReducibleState(0);
    const taylorFunction* I[3]= {&G,&J,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt)) return 0;
    }
    error::printTime("vor done! ");
    return 1;
    }


int C672796958() // III.App. vor0A+0.419351 sol
	{
	domain x,z;
	interval tx[6]={"4","4","4","8","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	// Upper bound of 3.76 was verified in Mathematica.
	interval tz[6]={s6,s6,s6,"14.14",s6,s6}; // 14.14>3.76^2.
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::lowVorVc
		+taylorSimplex::sol*"0.419351"
		+taylorSimplex::unit*"-0.3072";
	F.setReducibleState(1);
	domain x0=x,z0=z;
	const taylorFunction* I[1] = {&F};
    cellOption opt;
	opt.setDihMax(2.1201);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,1,opt);
	}

int C642039701() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"-1"
		+taylorSimplex::unit*"1.487741"
		+taylorSimplex::y1*"-0.377076"
		+taylorSimplex::y2*"-0.377076"
		+taylorSimplex::y3*"-0.377076"
		+taylorSimplex::y4*"0.221"
		+taylorSimplex::y5*"0.221"
		+taylorSimplex::y6*"0.221";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return generic2(x,z,F,G);
	}

int C999406873() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol
		+taylorSimplex::unit*"0.76822"
		+taylorSimplex::y4*"-0.221"
		+taylorSimplex::y5*"-0.221"
		+taylorSimplex::y6*"-0.221";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return generic2(x,z,F,G);
	}

int C583956642() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::dih*"-1"
		+taylorSimplex::unit*"2.29295"
		+taylorSimplex::y2*"-0.34"
		+taylorSimplex::y3*"-0.34"
		+taylorSimplex::y4*"0.689"
		+taylorSimplex::y5*"-0.27"
		+taylorSimplex::y6*"-0.27";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return generic2(x,z,F,G);
	}

int C301255700() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::dih
		+taylorSimplex::unit*"0.37884"
		+taylorSimplex::y1*"-0.498"
		+taylorSimplex::y4*"-0.731"
		+taylorSimplex::y5*"0.212"
		+taylorSimplex::y6*"0.212";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return generic2(x,z,F,G);
	}

int C652020790() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*"-1.5574737"
		+taylorSimplex::y1*"0.109"
		+taylorSimplex::y2*"0.109"
		+taylorSimplex::y3*"0.109"
		+taylorSimplex::y4*"0.14135"
		+taylorSimplex::y5*"0.14135"
		+taylorSimplex::y6*"0.14135";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return qrtet2(x,z,F,G);
	}

int C786938555() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"0.419351"
		+taylorSimplex::unit*"-1.77465"
		+taylorSimplex::y1*"0.2"
		+taylorSimplex::y2*"0.2"
		+taylorSimplex::y3*"0.2"
		+taylorSimplex::y4*"0.048"
		+taylorSimplex::y5*"0.048"
		+taylorSimplex::y6*"0.048";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return qrtet2(x,z,F,G);
	}

int C290675447() // III.App.6. no height restriction
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval t25("5.0625");
	interval tz[6]={s6,s6,s6,t25,t25,t25};
	z = domain::upperD(tz);
	taylorFunction F = 
		// -zeta pt =-0.100444...
		taylorQrtet::sol*"-0.1004445714270563950"
		+taylorSimplex::unit*"-1.48542"
		+taylorSimplex::y1*"0.0845696"
		+taylorSimplex::y2*"0.0845696"
		+taylorSimplex::y3*"0.0845696"
		+taylorSimplex::y4*"0.163"
		+taylorSimplex::y5*"0.163"
		+taylorSimplex::y6*"0.163";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"6.25"
		+taylorSimplex::y4*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(1);
	return qrtet2(x,z,F,G);
	}


int C99742666() // III.App.6.', 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval tz[6]={s6,s6,s6,s6,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"-1"
		+taylorSimplex::unit*"1.761445"
		+taylorSimplex::y1*"-0.378"
		+taylorSimplex::y2*"-0.378"
		+taylorSimplex::y3*"-0.378"
		+taylorSimplex::y4*"0.1781"
		+taylorSimplex::y5*"0.1781"
		+taylorSimplex::y6*"0.1781";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"-6.25"
		+taylorSimplex::y4
		+taylorSimplex::y5
		+taylorSimplex::y6;
	G.setReducibleState(0);
	return generic2(x,z,F,G);
	}

int C534430072() // III.App.6.', no ht restrictions
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval tz[6]={s6,s6,s6,s6,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol
		+taylorSimplex::unit*"0.489145"
		+taylorSimplex::y1*"0.171"
		+taylorSimplex::y2*"0.171"
		+taylorSimplex::y3*"0.171"
		+taylorSimplex::y4*"-0.3405"
		+taylorSimplex::y5*"-0.3405"
		+taylorSimplex::y6*"-0.3405";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"-6.25"
		+taylorSimplex::y4
		+taylorSimplex::y5
		+taylorSimplex::y6;
	G.setReducibleState(0);
	return generic2(x,z,F,G);
	}

int C769119384() // III.App.6.', no ht restrictions
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval tz[6]={s6,s6,s6,s6,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*"-1.2436"
		+taylorSimplex::y1*"0.1208"
		+taylorSimplex::y2*"0.1208"
		+taylorSimplex::y3*"0.1208"
		+taylorSimplex::y4*"0.0781"
		+taylorSimplex::y5*"0.0781"
		+taylorSimplex::y6*"0.0781";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"-6.25"
		+taylorSimplex::y4
		+taylorSimplex::y5
		+taylorSimplex::y6;
	G.setReducibleState(0);
	return qrtet2(x,z,F,G);
	}

int C942925387() // III.App.6.', no ht restrictions
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval tz[6]={s6,s6,s6,s6,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"0.419351"
		+taylorSimplex::unit*"-1.40816"
		+taylorSimplex::y1*"0.2"
		+taylorSimplex::y2*"0.2"
		+taylorSimplex::y3*"0.2"
		+taylorSimplex::y4*"-0.0106"
		+taylorSimplex::y5*"-0.0106"
		+taylorSimplex::y6*"-0.0106";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"-6.25"
		+taylorSimplex::y4
		+taylorSimplex::y5
		+taylorSimplex::y6;
	G.setReducibleState(0);
	return qrtet2(x,z,F,G);
	}

int C630241868() // III.App. final dih.
	{
	domain x,z;
	interval s8("8.5849");
	interval tx[6]={"4","4","4",s8,"4","4"};
	x = domain::lowerD(tx);
	interval s6("6.3001");
	interval s3("4.5369"); // 2.13^2
	interval tz[6]={s3,s3,s3,s8,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"1.694";
	F.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"8.709"
		+taylorSimplex::y2*"-1"
		+taylorSimplex::y3*"-1"
		+taylorSimplex::y5*"-1"
		+taylorSimplex::y6*"-1";
	G.setReducibleState(0);
	return generic2(x,z,F,G);
	}

int C972447547() // III.App. final dih.
	{
	domain x,z;
	interval tx[6]={"4","4","4","8","4","4"};
	x = domain::lowerD(tx);
	interval s8("8.5849");
	interval s6("6.3001");
	interval s3("4.5369"); // 2.13^2
	interval tz[6]={s3,s3,s3,s8,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih2*"-1"
		+taylorSimplex::unit*"2.6506"
		+taylorSimplex::y1*"-0.59"
		+taylorSimplex::y2*"-0.1"
		+taylorSimplex::y3*"-0.1"
		+taylorSimplex::y4*"-0.55"
		+taylorSimplex::y5*"0.6"
		+taylorSimplex::y6*"0.12"
		;
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C439095236() // III.App. final dih.
	{
	domain x,z;
	interval tx[6]={"4","4","4","8","4","4"};
	x = domain::lowerD(tx);
	interval s8("8.5849");
	interval s6("6.3001");
	interval s3("4.5369"); // 2.13^2
	interval tz[6]={s3,s3,s3,s8,s6,s6};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih2
		+taylorSimplex::unit*"-0.47"
		+taylorSimplex::y1*"0.35"
		+taylorSimplex::y2*"-0.24"
		+taylorSimplex::y3*"0.05"
		+taylorSimplex::y4*"0.35"
		+taylorSimplex::y5*"-0.72"
		+taylorSimplex::y6*"-0.18"
		;
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}



main()
	{
	selfTest();
	/*
	if (C642039701()) // 
		cout << "C642039701 done"; else cout << "NO!" ;
		cout << endl;
	if (C999406873()) // 
		cout << "C6999406873 done"; else cout << "NO!" ;
		cout << endl;
	if (C583956642()) // 
		cout << "C583956642 done"; else cout << "NO!" ;
		cout << endl;
	if (C301255700()) // 
		cout << "C301255700 done"; else cout << "NO!" ;
		cout << endl;
	if (C652020790()) // 
		cout << "C652020790 done"; else cout << "NO!" ;
		cout << endl;
	if (C786938555()) // 
		cout << "C786938555 done"; else cout << "NO!" ;
		cout << endl;
	if (C290675447()) // 
		cout << "C290675447 done"; else cout << "NO!" ;
		cout << endl;

	if (C99742666()) // 
		cout << "C99742666 done"; else cout << "NO!" ;
		cout << endl;
	if (C534430072()) // 
		cout << "C534430072 done"; else cout << "NO!" ;
		cout << endl;
	*/
	if (C672796958()) // 
		cout << "C672796958 done"; else cout << "NO!" ;
		cout << endl;
	/*
	if (C769119384()) // 
		cout << "C769119384 done"; else cout << "NO!" ;
		cout << endl;
	if (C942925387()) // 
		cout << "C942925387 done"; else cout << "NO!" ;
		cout << endl;

	if (C630241868())
		cout << "C630241868 done"; else cout << "NO!" ;
		cout << endl;
	if (C972447547())
		cout << "C972447547 done"; else cout << "NO!" ;
		cout << endl;
	if (C439095236())
		cout << "C439095236 done"; else cout << "NO!" ;
		cout << endl;

	*/
	error::printTime();
	}
