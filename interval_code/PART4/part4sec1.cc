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
int generic2_246(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[2] = {&F,&G};
    cellOption opt;
	opt.setDihMax(2.4601);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt);
    }

// generic with 2.46 dihedral max cutoff.
int generic_246(const domain& x,const domain& z,const taylorFunction& F)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[1] = {&F};
    cellOption opt;
	opt.setDihMax(2.4601);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,1,opt);
    }


int UpNuQuarter(interval a,interval b) // A2
    { 
	// Prove nu - a - b dih < 0.
    /*gammaNu*/{
	domain x,z;
    domain x0,z0;
	setupright(x,z,x0,z0);
    taylorFunction F = gammaNu
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    taylorFunction G = taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
    taylorFunction H = taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
    F.setReducibleState(0);
    G.setReducibleState(1);
    H.setReducibleState(1);
    const taylorFunction* I[3]= {&F,&G,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt)) return 0;
    }
    error::printTime("gamma done! ");
    /*vor*/{
	domain x,z;
    domain x0,z0;
	setupright(x,z,x0,z0);
    taylorFunction F = vorNu
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    taylorFunction H = taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
	F.setReducibleState(0);
    H.setReducibleState(0);
    const taylorFunction* I[2]= {&F,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt)) return 0;
    }
    error::printTime("vor done! ");
    return 1;
    }

int UpTauQuarter(interval a,interval b) // A3
	{
	// Prove -taunu - a - b dih < 0.
    /*tauGNu*/{
	domain x,z;
    domain x0,z0;
	setupright(x,z,x0,z0);
    taylorFunction F = tauGNu*"-1"
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    taylorFunction G = taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
    taylorFunction H = taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
    F.setReducibleState(0);
    G.setReducibleState(1);
    H.setReducibleState(1);
    const taylorFunction* I[3]= {&F,&G,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt)) return 0;
    }
    error::printTime("gamma done! ");
    /*tauVNu*/{
	domain x,z;
    domain x0,z0;
	setupright(x,z,x0,z0);
    taylorFunction F = tauVNu*"-1"
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    taylorFunction H = taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
	F.setReducibleState(0);
    H.setReducibleState(0);
    const taylorFunction* I[2]= {&F,&H};
    cellOption opt;
    if (!prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt)) return 0;
    }
    error::printTime("vor done! ");
    return 1;
    }

int TypeCScore(interval a,interval b) // A4
	//Example: case 649592321: t=TypeCScore("-3.421","2.28501");
	{
	// Prove vorx < a + b dih.
	// Case 1. y4>2.77,  vorVc scoring. (vor<vorVc, so this is OK).
	// Case 2. y4<2.77,  vor
 
    /*Case1*/{
	domain x,z;
    domain x0,z0;
	setC(x,z,x0,z0);
	interval tx[6]={"6.3001","4","4",/*2.77^2=*/"7.6729","4","4"};
	x = domain::lowerD(tx);
	x0= domain::lowerD(tx);
    taylorFunction F = taylorSimplex::highVorVc
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    F.setReducibleState(1);
	if (!generic_246(x,z,F)) return 0;
    }
    error::printTime("Case 1 done! ");
 
    /*Case2*/{
	domain x,z;
    domain x0,z0;
	setC(x,z,x0,z0);
    interval tz[6]={"8","6.3001","6.3001",/*2.77^2*/"7.6729","6.3001","6.3001"};
	z = domain::upperD(tz);
	z0= domain::upperD(tz);
    taylorFunction F = taylorSimplex::vor
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    F.setReducibleState(1);
	if (!generic_246(x,z,F)) return 0;
    }
    error::printTime("type C done! ");
    return 1;
    }

int TypeCSquander(interval a,interval b) // A5
	//Example: case 719735900: t=TypeCSquander("-3.3407","2.1747");
	{
	// Prove -taux < a + b dih.
	// Prove vorx < a + b dih.
	// Case 1. y4>2.77,  tauVc scoring. (tauV>tauVc, so this is OK).
	// Case 2. y4<2.77,  tauV
 
    /*Case1*/{
	domain x,z;
    domain x0,z0;
	setC(x,z,x0,z0);
	interval tx[6]={"6.3001","4","4",/*2.77^2=*/"7.6729","4","4"};
	x = domain::lowerD(tx);
	x0= domain::lowerD(tx);
    taylorFunction F = highTauVc*"-1"
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    F.setReducibleState(1);
	if (!generic_246(x,z,F)) return 0;
    }
    error::printTime("Case 1 done! ");



    /*Case2*/{
	domain x,z;
    domain x0,z0;
	setC(x,z,x0,z0);
    interval tz[6]={"8","6.3001","6.3001",/*2.77^2*/"7.6729","6.3001","6.3001"};
	z = domain::upperD(tz);
	z0= domain::upperD(tz);
    taylorFunction F = tauAnalytic*"-1"
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    F.setReducibleState(1);
	if (!generic_246(x,z,F)) return 0;
    }
    error::printTime("type C done! ");
    return 1;
    }

int AnchoredVor(interval a,interval b) // A6
	//Example: case 555481748: t=AnchoredVor("-3.58","2.28501");
	{
	domain x,z;
    domain x0,z0;
	setANC(x,z,x0,z0);
    taylorFunction F = taylorSimplex::highVorVc
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
	taylorFunction G = taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"2.46";
    F.setReducibleState(1);
	G.setReducibleState(1);
	return (generic2_246(x,z,F,G));
    }
 

int AnchoredTau(interval a,interval b) // A7
	//Example: case 679673664: t=AnchoredTau("-3.48","2.1747");
	{
	domain x,z;
    domain x0,z0;
	setANC(x,z,x0,z0);
    taylorFunction F = highTauVc*"-1"
		+taylorSimplex::unit*(-a)
		+taylorUpright::dih*(-b);
    F.setReducibleState(1);
	taylorFunction G = taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"2.46";
	return (generic2_246(x,z,F,G));
    }

int DihLower(interval tx[6],interval tz[6],interval bd) // A8
	//Example: t=DihLower(x,z,"1.23");
	{
	domain x,z;
    domain x0,z0;
	x=x0=domain::lowerD(tx);
	z=z0=domain::upperD(tz);
    taylorFunction F = taylorSimplex::dih*"-1";
    F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

void verify(int identifier) 
	{
	cout << "Begin verification of " << identifier << endl;
	error::printTime();
	int t;
	switch(identifier)
		{
		// Section A1:
		case 275706375:
			{
			domain x,z;
			interval t("6.3001");
			interval u("7.6729"); // 2.77^2;
			setLower(x,"4","4","4",u,"4","4");
			setUpper(z,t,t,t,"8",t,t);
			taylorFunction F = taylorFlat::vor1385
				+taylorSimplex::unit*"-0.00005";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			F.setReducibleState(1);
			G.setReducibleState(0);
			generic2(x,z,F,G);
			}
			break;

		case 324536936:
			{
			domain x,z;
			interval t("6.3001");
			interval u("7.6729"); // 2.77^2;
			setLower(x,"4","4","4",u,"4","4");
			setUpper(z,t,t,t,"8",t,t);
			taylorFunction F = taylorFlat::vor1385
				+taylorSimplex::unit*"-0.00005";
			taylorFunction G = taylorSimplex::eta2_234
				+taylorSimplex::unit*"-2";
			F.setReducibleState(1);
			G.setReducibleState(0);
			generic2(x,z,F,G);
			}
			break;

		case 983547118:
			{
			domain x,z;
			interval t("6.3001");
			interval u("7.6729"); // 2.77^2;
			setLower(x,"4","4","4",u,"4","4");
			setUpper(z,t,t,t,"8",t,t);
			taylorFunction F = taylorFlat::vor1385
				+taylorFlat::sol*(-zetapt)
				+taylorSimplex::unit*"0.0682";
			taylorFunction G = taylorSimplex::eta2_456
				+taylorSimplex::unit*"-2";
			F.setReducibleState(1);
			G.setReducibleState(0);
			generic2(x,z,F,G);
			}
			break;

		case 206278009:
			{
			domain x,z;
			interval t("6.3001");
			interval u("7.6729"); // 2.77^2;
			setLower(x,"4","4","4",u,"4","4");
			setUpper(z,t,t,t,"8",t,t);
			taylorFunction F = taylorFlat::vor1385
				+taylorFlat::sol*(-zetapt)
				+taylorSimplex::unit*"0.0682";
			taylorFunction G = taylorSimplex::eta2_234
				+taylorSimplex::unit*"-2";
			F.setReducibleState(1);
			G.setReducibleState(0);
			generic2(x,z,F,G);
			}
			break;

		// Section A2:
		case 413688580: t=UpNuQuarter("-4.3223","4.10113");
			break;
		case 805296510: t=UpNuQuarter("-0.9871","0.80449");
			break;
		case 136610219: t=UpNuQuarter("-0.8756","0.70186");
			break;
		case 379204810: t=UpNuQuarter("-0.3404","0.24573");
			break;
		case 878731435: t=UpNuQuarter("-0.0024","0.00154");
			break;
		case 891740103: t=UpNuQuarter("0.1196","-0.07611");
			break;

		// Section A3:
		case 334002329: t=UpTauQuarter("-4.42873","4.16523");
			break;
		case 883139937: t=UpTauQuarter("-1.01104","0.78701");
			break;
		case 507989176: t=UpTauQuarter("-0.99937","0.77627");
			break;
		case 244435805: t=UpTauQuarter("-0.34877","0.21916");
			break;
		case 930176500: t=UpTauQuarter("-0.11434","0.05107");
			break;
		case 815681339: t=UpTauQuarter("0.07749","-0.07106");
			break;

		// Section A4
		case 649592321: t=TypeCScore("-3.421","2.28501");
			break;
		case 600996944: t=TypeCScore("-2.616","1.67382");
			break;
		case 70667639: t=TypeCScore("-1.4486","0.8285");
			break;
		case 99182343: t=TypeCScore("-0.79","0.390925");
			break;
		case 578762805: t=TypeCScore("-0.3088","0.12012");
			break;
		case 557125557: t=TypeCScore("-0.1558","0.0501");
			break;

		// Section A5
		case 719735900: t=TypeCSquander("-3.3407","2.1747");
			break;
		case 359616783: t=TypeCSquander("-2.945","1.87427");
			break;
		case 440833181: t=TypeCSquander("-1.5035","0.83046");
			break;
		case 578578364: t=TypeCSquander("-1.0009","0.48263");
			break;
		case 327398152: t=TypeCSquander("-0.7787","0.34833");
			break;
		case 314861952: t=TypeCSquander("-0.4475","0.1694");
			break;
		case 234753056: t=TypeCSquander("-0.2568","0.0822");
			break;

		// Section A6
		case 555481748: t=AnchoredVor("-3.58","2.28501");
			break;
		case 615152889: t=AnchoredVor("-2.715","1.67382");
			break;
		case 647971645: t=AnchoredVor("-1.517","0.8285");
			break;
		case 516606403: t=AnchoredVor("-0.858","0.390925");
			break;
		case 690552204: t=AnchoredVor("-0.358","0.12012");
			break;
		case 852763473: t=AnchoredVor("-0.186","0.0501");
			break;

		// Section A7
		case 679673664: t=AnchoredTau("-3.48","2.1747");
			break;
		case 926514235: t=AnchoredTau("-3.06","1.87427");
			break;
		case 459744700: t=AnchoredTau("-1.58","0.83046");
			break;
		case 79400832: t=AnchoredTau("-1.06","0.48263");
			break;
		case 277388353: t=AnchoredTau("-0.83","0.34833");
			break;
		case 839852751: t=AnchoredTau("-0.5","0.1694");
			break;
		case 787458652: t=AnchoredTau("-0.29","0.0822");
			break;

		// Section A8.

		case 499014780: 
			{
			interval x[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
			interval z[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
			t=DihLower(x,z,"1.23");
			}
			break;

		case 901845849: 
			{
			interval x[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
			interval z[6]={"8","6.3001","6.3001","8","6.3001","6.3001"};
			t=DihLower(x,z,"1.4167");
			}
			break;

		case 410091263: 
			{
			interval x[6]={"6.3001","6.3001","6.3001","10.24","6.3001","6.3001"};
			interval z[6]={"8","6.3001","6.3001","10.24","6.3001","6.3001"};
			t=DihLower(x,z,"1.65");
			}
			break;

		case 125103581: 
			{
			interval x[6]={"6.3001","4","4","4","4","4"};
			interval z[6]={"8","6.3001","6.3001","4","6.3001","6.3001"};
			t=DihLower(x,z,"0.956");
			}
			break;

		case 504968542: 
			{
			interval x[6]={"6.3001","4","4","4","4","4"};
			interval z[6]={"8","6.3001","6.3001","4","8","6.3001"};
			t=DihLower(x,z,"0.28");
			}
			break;

		case 770716154: 
			{
			interval x[6]={"7.6729","6.3001","6.3001","10.24","6.3001","6.3001"};
			interval z[6]={"8","6.3001","6.3001","10.24","6.3001","6.3001"};
			t=DihLower(x,z,"1.714");
			}
			break;

		case 666090270: 
			{
			interval x[6]={"6.3001","5.0625","6.3001","10.24","6.3001","6.3001"};
			interval z[6]={"8","5.0625","6.3001","10.24","6.3001","6.3001"};
			t=DihLower(x,z,"1.714");
			}
			break;

		default : t=0; error::message("missing case"); break;

		}

		
		
	
	if (t) cout << "Verification complete" << endl;
	else cout << "FAIL! " << identifier << endl;
	error::printTime();
	}

void Section(char* s)
	{
	selfTest();
	cout << "\n\nSection " << s << endl << endl;
	}

void testBUG()
	{
	cout.precision(16);
	interval zlo[6]={"6.299538435010833","6.106430274361399",
	"6.150232343516342"," 6.113239249855036","5.399841126743369","4.746249674977873" };
	interval zhi[6]={"6.299538438978137","6.106430493404949","6.150233268920648",
	"6.113239759107179","5.399846779084382","4.746251246042092" };
	domain x = domain::lowerD(zlo);
	domain z = domain::upperD(zhi);
	taylorInterval f = taylorSimplex::vorSqc.evalf(x,z);
	cout << "f.upperPartial(3) = " << f.upperPartial(3) << endl;
	cout << "f.centerPoint.partial(3) = " << f.centerPoint.partial(3) << endl;
	int i,j;
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		{
		cout << "("<<i<<j<<")"<< f.DD[i][j] << endl;
		}//cout << "taylor err = " << 
	}

int main()
	{

	/*
	Section("A1");
	verify(275706375);
	verify(324536936);
	verify(983547118);
	verify(206278009);

	Section ("A2");
	verify(413688580);
	verify(805296510);
	verify(136610219);
	verify(379204810);
	verify(878731435);
	verify(891740103);

	Section("A3");
	verify(334002329);
	verify(883139937);
	verify(507989176);
	verify(244435805);
	verify(930176500);
	verify(815681339);

	Section("A4");
	verify(649592321);
	verify(600996944);
	verify(70667639);
	verify(99182343);
	verify(578762805);
	verify(557125557);

	Section("A5");
	verify(719735900);
	verify(359616783);
	verify(440833181);
	verify(578578364);
	verify(327398152);
	verify(314861952);
	verify(234753056);

	Section("A6");
	verify(555481748);
	verify(615152889);
	verify(647971645);
	verify(516606403);
	verify(690552204);
	verify(852763473);
	*/
	Section("A7");
	verify(679673664);
	verify(926514235);
	verify(459744700);
	verify(79400832);
	verify(277388353);
	verify(839852751);
	verify(787458652);
	/*

	Section("A8");
	verify(499014780);
	verify(901845849);
	verify(410091263);
	verify(125103581);
	verify(504968542);
	verify(770716154);
	verify(666090270);

	*/
	cout << "all done!" << endl;

	}
