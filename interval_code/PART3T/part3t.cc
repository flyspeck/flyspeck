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
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    }

	////////
	// This runs the asymmetric verification on a quad cluster
	// with the short edge drawn.
	//
int openQ(const taylorFunction& FA,const taylorFunction& FB,
	cellOption opt)
	{
	domain xA,xB,zA,zB;
	interval x[6]={"4","4","4","8","4","4"};
	xB = xA = domain::lowerD(x);
	interval v("6.3001");
	interval z[6]={v,v,v,"12.6002",v,v};
	zB = zA = domain::upperD(z);
	if (!FA.getReducibleState() ||
		!FB.getReducibleState())
		{
		error::message(
		 "Program is unlikely to terminate without reducibility");
		}
	const taylorFunction* IA[1]={&FA};
	const taylorFunction* IB[1]={&FB};
	prove::recursiveVerifierQ(0,xA,xB,zA,zB,IA,IB,1,opt);
	return 1;
	}

	////////
	// The verification of a "standard" quad cluster inequality
	// using vorVc.
	// vorVc < rhsC + rhsDIH dih + rhsSOL sol.
	//
int standardQ(interval rhsSOL,interval rhsDIH,interval rhsC)
	{
	static const interval zero("0");
	cout << "running standardQ(sol,dih,const)= " << rhsSOL << " "
		 << rhsDIH << " " << rhsC << endl << flush;
	/*asymmetric*/{
	taylorFunction FA= taylorSimplex::lowVorVc
		+taylorSimplex::unit*(-rhsC)
		+taylorSimplex::dih*(-rhsDIH)
		+taylorSimplex::sol*(-rhsSOL);
	taylorFunction FB= taylorSimplex::lowVorVc
		+taylorSimplex::sol*(-rhsSOL);
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	// an examination of the symmetries of the 18 cases gives...
	int skippable[7] = {7,8,9,10,12,14,16};
	opt.setSkipCases(skippable,7);
	openQ(FA,FB,opt);
	error::printTime("asymmetric phase complete ");
	}
 
	/*split*/{
	taylorFunction FA= taylorSimplex::lowVorVc
		+taylorSimplex::unit*(-rhsC)
		+taylorSimplex::dih2*(-rhsDIH)
		+taylorSimplex::sol*(-rhsSOL);
	taylorFunction FB= taylorSimplex::lowVorVc
		+taylorSimplex::dih2*(-rhsDIH)
		+taylorSimplex::sol*(-rhsSOL);
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	// an examination of the split symmetries of the 18 cases gives...
	int skippable[6] = {3,5,7,9,15,16};
	opt.setSkipCases(skippable,6);
	openQ(FA,FB,opt);
	error::printTime("split phase complete ");
	}
	return 1;
	}

// sol,dih,const on rhs...
// #7,#11 will be done separately with Sqc truncation.
int C178457604() { return standardQ("0","4.56766","-5.7906"); }
int C157809242() { return standardQ("0","1.5094","-2.0749"); }
int C642828564() { return standardQ("0","0.5301","-0.8341"); }
int C863478300() { return standardQ("0","0.3878","-0.6284"); }
int C481399994() { return standardQ("0","-0.1897","0.4124"); }
int C821979005() { return standardQ("0","-0.5905","1.5707"); } // #6
int C174945773() { return standardQ("-0.3","0","0.41717"); } // #7
	// #7 here shouldn't pass.  If it does, something is wrong...
	// because we need truncation at sqrt(2) to get it through.
static const interval zetapt("0.100444571427056395000");
int C42457607() { return standardQ(zetapt,"4.49461","-5.81446"); } // #8
int C243293590() { return standardQ(zetapt,"2.1406","-2.955"); } // #9
int C922768071() { return standardQ(zetapt,"0.316","-0.6438"); } // #10
int C122485214() { return standardQ(zetapt,"-0.2365","0.3825"); } // #12
int C939438357() { return standardQ(zetapt,"-0.4747","1.071"); } // #13
static const interval zetapt32= zetapt*interval("3.2");
int C615676717() { return standardQ(zetapt32,"4.25863","-5.77942"); } // #14
int C843184574() { return standardQ(zetapt32,"3.5294","-4.893"); } // #15
int C820433806() { return standardQ(zetapt32,"0","-0.4126"); } // #16
int C995492817() { return standardQ(zetapt32,"-0.316","0.33"); } // #17
static const interval ax("0.419351");
int C90332908() { return standardQ(-ax,"4.611391","-5.350181"); } // #18
int C35981987() { return standardQ(-ax,"1.582508","-1.66174"); } // #19
int C364734367() { return standardQ(-ax,"0.342747","0.0895"); } // #20
int C902843884() { return standardQ(-ax,"-0.974137","3.36909"); } // #21

	////////
	// The verification of a "standard" quad cluster 4.2 inequality
	// using vorVc.
	// vorVc < rhsC + rhsD d.
	// d = dih1 + dih2. There are not two cases as in standardQ,
	// but there are also no symmetries.
	//
int standard42(interval rhsD,interval rhsC)
	{
	static const interval zero("0");
	cout << "running standard42(d,const)= " 
		 << rhsD << " " << rhsC << endl << flush;
	taylorFunction FA= taylorSimplex::lowVorVc
		+taylorSimplex::unit*(-rhsC)
		+taylorSimplex::dih*(-rhsD)
		+taylorSimplex::dih2*(-rhsD);
	taylorFunction FB= taylorSimplex::lowVorVc
		+taylorSimplex::dih2*(-rhsD);
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	openQ(FA,FB,opt);
	error::printTime("standard 42 verification complete ");
	return 1;
	}

int C385278991() { return standard42("3.0508","-9.494"); } // #4.2.1.
int C647779082() { return standard42("-0.844","3.5926"); } // #4.2.4.

	////////
	// standardSqc is designed espeically for Calcs III.4.1.7 and III.4.1.11.
	// These do not pass, if the upper approximation vorVc is used.
	// Instead we do two cases: vorSqc, and (3/4)vorVc+(1/4)(-1.04pt).
	// These two calculations do not have a dihedral term, so we can reduce the
	// number of cases by symmetries.  Also if the diagonal drops to sqrt(8) by dimension
	// reduction, then the inequalities break into two identical halves, so we
	// remove cases 11,12,13,14,15,16,17 and replace them with a simplex interval calculation.
	//
int standardSqc(interval rhsSOL,interval rhsC)
	{
	static const interval zero("0");
	static const interval shift("-0.014397147873800606"); // -1.04 pt/4.
	cout << "running standardSqc(sol,const)= " 
		 << rhsSOL << " " << rhsC << endl << flush;
	{
	taylorFunction FA= 
		taylorSimplex::lowVorVc*"0.75"+taylorSimplex::unit*shift
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::sol*(-rhsSOL);
	taylorFunction FB= FA;
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	// an examination of the symmetries of the 18 cases with no dihedral term gives...
	int skippable[13] = {3,5,7,8,9,10,11,12,13,14,15,16,17};
	opt.setSkipCases(skippable,13);
	openQ(FA,FB,opt);
 
	// now start short diag case...
    interval tx[6]={"4","4","4","8","4","4"};
    interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
    domain x = domain::lowerD(tx);
    domain z = domain::lowerD(tz);
    if (!prove::generic(x,z,FA)) 
		{ error::message("generic failed on VorVc"); return 0;}
	error::printTime("vorVc (3/4) -1.04 pt (1/4) verification complete ");
	}
 
	{
	taylorFunction FA= 
		taylorSimplex::vorSqc
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::sol*(-rhsSOL);
	taylorFunction FB= FA;
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	// an examination of the symmetries of the 18 cases with no dihedral term gives...
	int skippable[13] = {3,5,7,8,9,10,11,12,13,14,15,16,17};
	opt.setSkipCases(skippable,13);
	openQ(FA,FB,opt);
 
	// now start short diag case...
    interval tx[6]={"4","4","4","8","4","4"};
    interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
    domain x = domain::lowerD(tx);
    domain z = domain::lowerD(tz);
    if (!prove::generic(x,z,FA)) 
		{ error::message("generic failed on Sqc") ; return 0; }
	error::printTime("vorSqc verification complete ");
	}
	return 1;
	}

									// sol,      const.
int C566974163() { return standardSqc("-0.3","0.41717"); } // #4.2.7.
int C967248505() { return standardSqc(zetapt,"-0.1317"); } // #4.2.11

	////////
	// standardSqc42 is designed especially for Calcs III.4.2.2 and III.4.2.3.
	// These do not pass, if the upper approximation vorVc is used.
	// Instead we do two cases: vorSqc, and (3/4)vorVc+(1/4)(-1.04pt).
	// We can reduce the
	// number of cases by symmetries.  
	//
int standardSqc42(interval rhsDIH,interval rhsC)
	{
	static const interval zero("0");
	static const interval shift("-0.014397147873800606"); // -1.04 pt/4.
	cout << "running standardSqc42(dih,const)= " 
		 << rhsDIH << " " << rhsC << endl << flush;
	{
	taylorFunction FA= 
		taylorSimplex::lowVorVc*"0.75"+taylorSimplex::unit*shift
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::dih2*(-rhsDIH)
		+taylorSimplex::dih*(-rhsDIH);
	taylorFunction FB= 
		taylorSimplex::lowVorVc*"0.75"+taylorSimplex::unit*shift
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::dih2*(-rhsDIH);
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	openQ(FA,FB,opt);
	error::printTime("vorVc (3/4) -1.04 pt (1/4) verification complete ");
	}
 
	{
	taylorFunction FA= 
		taylorSimplex::vorSqc
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::dih2*(-rhsDIH)
		+taylorSimplex::dih*(-rhsDIH);
	taylorFunction FB= 
		taylorSimplex::lowVorVc*"0.75"+taylorSimplex::unit*shift
		+taylorSimplex::unit*(-rhsC/interval("2"))
		+taylorSimplex::dih2*(-rhsDIH);
	FA.setReducibleState(1);
	FB.setReducibleState(1);
	cellOption opt;
	openQ(FA,FB,opt);
	error::printTime("vorSqc42 verification complete ");
	}
	return 1;
	}
							// dih,      const.
int C943202595() { return standardSqc42("0.27605","-1.0472"); } // #4.2.2.
int C338082609() { return standardSqc42("-0.198867","0.7624"); } // #4.2.3.

main()
	{
	selfTest();
	/*
	if (C178457604()) // #1
		cout << "C178457604 done"; else cout << "NO!" ;
		cout << endl;
	if (C157809242())  // #2
		cout << "C157809242 done"; else cout << "NO!" ;
		cout << endl;
	if (C642828564()) // #3
		cout << "C642828564 done"; else cout << "NO!" ;
		cout << endl;
	if (C863478300()) // #4
		cout << "C863478300 done"; else cout << "NO!" ;
		cout << endl;
	if (C481399994()) // #5
		cout << "C481399994 done"; else cout << "NO!" ;
		cout << endl;
	if (C821979005()) // #6
		cout << "C821979005 done"; else cout << "NO!" ;
		cout << endl;
	*/
	if (C174945773()) // #7 (false version, Vc truncation)
		cout << "C174945773 done"; else cout << "NO!" ;
		cout << endl;
	/*
	if (C42457607()) // #8
		cout << "C42457607 done"; else cout << "NO!" ;
		cout << endl;
	if (C243293590()) // #9
		cout << "C243293590 done"; else cout << "NO!" ;
		cout << endl;
	if (C922768071()) // #10
		cout << "C922768071 done"; else cout << "NO!" ;
		cout << endl;
	if (C122485214()) // #12
		cout << "C122485214 done"; else cout << "NO!" ;
		cout << endl;
	if (C939438357()) // #13
		cout << "C939438357 done"; else cout << "NO!" ;
		cout << endl;
	if (C615676717()) // #14
		cout << "C615676717 done"; else cout << "NO!" ;
		cout << endl;
	if (C843184574()) // #15
		cout << "C843184574 done"; else cout << "NO!" ;
		cout << endl;
	if (C820433806()) // #16
		cout << "C820433806 done"; else cout << "NO!" ;
		cout << endl;
	if (C995492817()) // #17
		cout << "C995492817 done"; else cout << "NO!" ;
		cout << endl;
	if (C90332908()) // #18
		cout << "C90332908 done"; else cout << "NO!" ;
		cout << endl;
	if (C35981987()) // #19
		cout << "C35981987 done"; else cout << "NO!" ;
		cout << endl;
	if (C364734367()) // #20
		cout << "C364734367 done"; else cout << "NO!" ;
		cout << endl;
	if (C902843884()) // #21
		cout << "C902843884 done"; else cout << "NO!" ;
		cout << endl;
	if (C385278991()) // #4.2.1
		cout << "C385278991 done"; else cout << "NO!" ;
		cout << endl;
	if (C647779082()) // #4.2.4
		cout << "C647779082 done"; else cout << "NO!" ;
		cout << endl;
	if (C566974163()) // #7
		cout << "C566974163 done"; else cout << "NO!" ;
		cout << endl;
	if (C967248505()) // #11
		cout << "C967248505 done"; else cout << "NO!" ;
		cout << endl;
	if (C943202595()) // #4.2.2
		cout << "C943202595 done"; else cout << "NO!" ;
		cout << endl;
	if (C338082609()) // #4.2.3
		cout << "C338082609 done"; else cout << "NO!" ;
		cout << endl;
	*/


	error::printTime();
	}
