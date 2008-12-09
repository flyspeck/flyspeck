#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"

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

int C619245724() // Part III. 10. Group 3.1
	{
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.4111")
		+ taylorQrtet::dih*"-0.37898";
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C678284947() // Part III. 10. Group 3.2.
	{
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.23021")
		+ taylorQrtet::dih*"0.142";
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C970731712() // Part III. 10. Group 3.3
	{
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.5353")
		+ taylorQrtet::dih*"0.3302";
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C921602098() // Part III. 10. Group 3.4
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.4666")
		+ taylorQrtet::dih*"-0.3897"
		+ taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C338482233() // III.10.Group3.5
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.3683")
		+ taylorQrtet::dih*"-0.2993"
		+ taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C47923787() // III.10.Group3.6
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C156673846() // III.10.Group3.7
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.208")
		+ taylorQrtet::dih*"0.1689"
		+ taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C363044842() // III.10.Group3.8
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.3442")
		+ taylorQrtet::dih*"0.2529"
		+ taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C68229886() // III.10.Group3.9
	{
	static interval zetapt("0.1004445714270563950000");
	static interval zetapt32 = zetapt*interval("3.2");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.5974")
		+ taylorQrtet::dih*"-0.4233"
		+ taylorQrtet::sol*(-zetapt32);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C996335124() // III.10.Group3.10
	{
	static interval zetapt("0.1004445714270563950000");
	static interval zetapt32 = zetapt*interval("3.2");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.255")
		+ taylorQrtet::dih*"-0.1083"
		+ taylorQrtet::sol*(-zetapt32);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C722658871() // III.10.Group3.11
	{
	static interval zetapt("0.1004445714270563950000");
	static interval zetapt32 = zetapt*interval("3.2");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.0045")
		+ taylorQrtet::dih*"0.0953"
		+ taylorQrtet::sol*(-zetapt32);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C226224557() // III.10.Group3.12
	{
	static interval zetapt("0.1004445714270563950000");
	static interval zetapt32 = zetapt*interval("3.2");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.1369")
		+ taylorQrtet::dih*"0.1966"
		+ taylorQrtet::sol*(-zetapt32);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C914585134() // III.10.Group3.13
	{
	static interval ax("0.419351");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("0.5786316")
		+ taylorQrtet::dih*"-0.796456"
		+ taylorQrtet::sol*ax;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C296182719() // III.10.Group3.14
	{
	static interval ax("0.419351");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.211419")
		+ taylorQrtet::dih*"-0.0610397"
		+ taylorQrtet::sol*ax;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C538860011() // III.10.Group3.15
	{
	static interval ax("0.419351");
	domain x,z;
	setqr(x,z);
	// taylorFunction F = taylorSimplex::unit*("-0.3085626")
	taylorFunction F = taylorSimplex::unit*("-0.308526") // fixed 7/10/98
		+ taylorQrtet::dih*"0.0162028"
		+ taylorQrtet::sol*ax;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C886673381() // III.10.Group3.16
	{
	static interval ax("0.419351");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-0.35641")
		+ taylorQrtet::dih*"0.0499559"
		+ taylorQrtet::sol*ax;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C681494013() // III.10.Group3.17
	{
	static interval ax("0.419351");
	domain x,z;
	setqr(x,z);
	taylorFunction F = taylorSimplex::unit*("-1.3225")
		+ taylorQrtet::dih*"0.64713719"
		+ taylorQrtet::sol*ax;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}


int C357108142() // III.10.Group5.7
	{
	static interval zetapt("0.1004445714270563950000");
	static interval m("0.2384");
	static interval xi("2.1773");
	static interval xi2= xi*xi;
	static interval four("4");
	domain x,z;
	setqr(x,z);
	interval u[6]={four,four,four,xi2,xi2,xi2};
	z = domain::upperD(u);
	taylorFunction F = taylorSimplex::unit*(interval("-0.29349")*interval("3"))
		+ taylorQrtet::dih*m
		+ taylorQrtet::dih2*m
		+ taylorQrtet::dih3*m
		+ taylorQrtet::sol*(-zetapt);
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}

int C706389670() // III.10.Group5.7
	{
	static interval m("0.207045");
	static interval xi("2.177303");
	static interval xi2=xi*xi;
	static interval pt2etc("-0.819967158663072260539852316328");
	static interval four("4");
	domain x,z;
	setqr(x,z);
	interval u[6]={four,four,four,xi2,xi2,xi2};
	z = domain::upperD(u);
	taylorFunction F = taylorSimplex::unit*pt2etc
		+ taylorQrtet::dih*m
		+ taylorQrtet::dih2*m
		+ taylorQrtet::dih3*m;
	F.setReducibleState(1);
	return prove::qrtet(x,z,F);
	}




int C250597127() // III.10.Group4.6 (flat)
	{
	interval tx[6]={"4","4","4","6.3001","4","4"};
	interval tz[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	domain x = domain::lowerD(tx);
	domain z = domain::lowerD(tz);
	taylorFunction F = 
	  (taylorSimplex::y2+taylorSimplex::y3+
			taylorSimplex::y5+taylorSimplex::y6)*("-0.398") +
		taylorSimplex::y1*"0.3257" +
		taylorFlat::dih*"-1" +
		taylorSimplex::unit*"4.14938";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C229576653() // Prop 4.3.1
	{
	domain x,z;
	setqr(x,z);
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	taylorFunction F = taylorSimplex::dih*"-1"+taylorSimplex::unit*"1.153093";
	F.setReducibleState(1);
	return prove::generic (x,z,F);
	}

int C141552816() // Prop 4.3.2
	{
	interval tx[6]={"4","4","4","4","6.3001","4"};
	interval tz[6]={"6.3001","6.3001","6.3001","6.3001","8","6.3001"};
	domain x=domain::lowerD(tx);
	domain z=domain::upperD(tz);
	taylorFunction F = taylorSimplex::dih+
		taylorSimplex::unit*(interval("-3.2467")/interval("2"));
	F.setReducibleState(1);
	return prove::generic (x,z,F);
	}


int C842944296() // III.App.4.2.1, 4.2.2
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih2*"1"
		+taylorSimplex::unit*"-0.0123"
		+taylorSimplex::y2*"-0.35"
		+taylorSimplex::y1*"0.15"
		+taylorSimplex::y3*"0.15"
		+taylorSimplex::y5*"-0.7022"
		+taylorSimplex::y4*"0.17";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C675811884() // III.App.4.2.3, 4.2.4
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih2*"-1"
		+taylorSimplex::unit*"2.63363"
		+taylorSimplex::y1*"-0.631"
		+taylorSimplex::y2*"0.13"
		+taylorSimplex::y3*"-0.31"
		+taylorSimplex::y4*"-0.413"
		+taylorSimplex::y5*"0.58"
		+taylorSimplex::y6*"-0.025";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C351282394() // III.App.4.2.5, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih*"1"
		+taylorSimplex::unit*"0.3482"
		+taylorSimplex::y1*"-0.714"
		+taylorSimplex::y2*"0.221"
		+taylorSimplex::y3*"0.221"
		+taylorSimplex::y4*"-0.92"
		+taylorSimplex::y5*"0.221"
		+taylorSimplex::y6*"0.221";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C310454325() // III.App.4.2.6, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"2.37095"
		+taylorSimplex::y1*"0.315"
		+taylorSimplex::y2*"-0.3972"
		+taylorSimplex::y3*"-0.3972"
		+taylorSimplex::y4*"0.715"
		+taylorSimplex::y5*"-0.3972"
		+taylorSimplex::y6*"-0.3972";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C570886957() // III.App.4.2.7, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::sol*"1"
		+taylorSimplex::unit*"0.437235"
		+taylorSimplex::y1*"0.187"
		+taylorSimplex::y2*"0.187"
		+taylorSimplex::y3*"0.187"
		+taylorSimplex::y4*"-0.1185"
		+taylorSimplex::y5*"-0.479"
		+taylorSimplex::y6*"-0.479";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C684634355() // III.App.4.2.8, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::sol*"-1"
		+taylorSimplex::unit*"2.244"
		+taylorSimplex::y1*"-0.488"
		+taylorSimplex::y2*"-0.488"
		+taylorSimplex::y3*"-0.488"
		+taylorSimplex::y5*"0.334"
		+taylorSimplex::y6*"0.334";
	F.setReducibleState(0);
	return prove::generic (x,z,F);
	}

int C525219062() // III.App.4.2.9, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		// taylorSimplex::sigma*"1"
		taylorSimplex::unit*"-1.17401"
		+taylorSimplex::y1*"0.159"
		+taylorSimplex::y2*"0.081"
		+taylorSimplex::y3*"0.081"
		// +taylorSimplex::y4*"0.133"
		+taylorSimplex::y5*"0.133"
		+taylorSimplex::y6*"0.133";
	F.setReducibleState(0);
	return prove::flat(x,z,F);
	}

int C833691633() // III.App.4.2.10, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorFlat::sol*"0.419351"
		+taylorFlat::dih*"-0.079431"
		+taylorSimplex::unit*(interval("-0.1448")
								+interval("4")*interval("0.0436"))
		+taylorSimplex::y5*"-0.0436"
		+taylorSimplex::y6*"-0.0436";
	F.setReducibleState(0);
	return prove::flat(x,z,F);
	}

int C600504426() // III.App.4.2.11, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","6.3001","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*"-1.3452011435749994492"
		+taylorSimplex::y4*"0.197"
		+taylorSimplex::y5*"0.197"
		+taylorSimplex::y6*"0.197";
	F.setReducibleState(0);
	return prove::flat(x,z,F);
	}

int C84621256() // III.App.4.3.1, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::dih*"-1"
		+taylorSimplex::unit*"1.82419"
		+taylorSimplex::y1*"0.636"
		+taylorSimplex::y2*"-0.462"
		+taylorSimplex::y3*"-0.462"
		+taylorSimplex::y4*"0.82"
		+taylorSimplex::y5*"-0.462"
		+taylorSimplex::y6*"-0.462";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C702064613() // III.App.4.3.2, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::dih*"1"
		+taylorSimplex::unit*"0.75281"
		+taylorSimplex::y1*"-0.55"
		+taylorSimplex::y2*"0.214"
		+taylorSimplex::y3*"0.214"
		+taylorSimplex::y4*"-1.24"
		+taylorSimplex::y5*"0.214"
		+taylorSimplex::y6*"0.214";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C946080966() // III.App.4.3.3,  4.3.5
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::dih2*"-1"
		+taylorSimplex::unit*"2.5481"
		+taylorSimplex::y1*"-0.4"
		+taylorSimplex::y2*"0.15"
		+taylorSimplex::y3*"-0.09"
		+taylorSimplex::y4*"-0.631"
		+taylorSimplex::y5*"0.57"
		+taylorSimplex::y6*"-0.23";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C235983060() // III.App.4.3.4,  4.3.6
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::dih2*"1"
		+taylorSimplex::unit*"-0.3429"
		+taylorSimplex::y1*"0.454"
		+taylorSimplex::y2*"-0.34"
		+taylorSimplex::y3*"-0.154"
		+taylorSimplex::y4*"0.346"
		+taylorSimplex::y5*"-0.805";
		//+taylorSimplex::y6*"-0.23";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C257870816() // III.App.4.3.7, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::sol*"-1"
		+taylorSimplex::unit*"0.2618"
		//+taylorSimplex::y1*"0.454"
		+taylorSimplex::y2*"-0.065"
		+taylorSimplex::y3*"-0.065"
		+taylorSimplex::y4*"-0.061"
		+taylorSimplex::y5*"0.115"
		+taylorSimplex::y6*"0.115";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C262640426() // III.App.4.3.8, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::sol*"1"
		+taylorSimplex::unit*"0.2514"
		+taylorSimplex::y1*"0.293"
		+taylorSimplex::y2*"0.03"
		+taylorSimplex::y3*"0.03"
		+taylorSimplex::y4*"-0.12"
		+taylorSimplex::y5*"-0.325"
		+taylorSimplex::y6*"-0.325";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C211766431() // III.App.4.3.9, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		//taylorUpright::sol*"1"
		taylorSimplex::unit*"-0.59834"
		//+taylorSimplex::y1*"0.293"
		+taylorSimplex::y2*"0.054"
		+taylorSimplex::y3*"0.054"
		+taylorSimplex::y4*"0.083"
		+taylorSimplex::y5*"0.054"
		+taylorSimplex::y6*"0.054";
	F.setReducibleState(0);
	return prove::upright(x,z,F);
	}

int C702861263() // III.App.4.3.10, 
	{
	domain x,z;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorUpright::sol*"0.419351"
		+taylorSimplex::unit*(interval("-0.06904")+interval("-2.8")*interval("0.0846"))
		+taylorSimplex::y1*"0.0846"
		+taylorUpright::dih*"-0.079431"; // changed from -0.089431 7/10/98
	F.setReducibleState(0);
	return prove::upright(x,z,F);
	}

int C255518878() // III.App.4.3.11, 
	{
	domain x,z;
	interval t13("2.13");
	interval s=t13*t13;
	interval tx[6]={"6.3001","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"8",s,s,"6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*
		  (interval("0.07")*interval("2.51")
			+interval("-0.133")*interval("8")
			+interval("-0.135")*interval("2"))
		+taylorSimplex::y1*"-0.07"
		+taylorSimplex::y2*"0.133"
		+taylorSimplex::y3*"0.133"
		+taylorSimplex::y4*"0.135"
		+taylorSimplex::y5*"0.133"
		+taylorSimplex::y6*"0.133";
	F.setReducibleState(0);
	return prove::upright(x,z,F);
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


int C584917623() // III.App.4.6.1, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval tz[6]={"6.3001","6.3001","6.3001","5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"-1"
		+taylorSimplex::unit*
		  (interval("0.551285")-interval("0.221")*interval("6")
			+interval("0.377076")*interval("6"))
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

int C190861218() // III.App.4.6.2, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval tz[6]={"6.3001","6.3001","6.3001","5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol
		+taylorSimplex::unit*
		  (interval("-0.55778")+interval("0.221")*interval("6"))
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

int C957853434() // III.App.4.6.3, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::dih*"-1"
		+taylorSimplex::unit*
		  (interval("1.23095")+interval("0.27")*interval("8")
		  +interval("0.689")*interval("-2"))
		+taylorSimplex::y2*"-0.27"
		+taylorSimplex::y3*"-0.27"
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

int C880803585() // III.App.4.6.4, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::dih
		+taylorSimplex::unit*
		  (interval("-1.23116")+interval("-0.212")*interval("4")
		  +interval("0.489")*interval("2")
		  +interval("0.731")*interval("2"))
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


int C193930450() // III.App.4.6.5, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*
		  (interval("-0.0553737")+interval("-0.14135")*interval("12"))
		+taylorSimplex::y1*"0.14135"
		+taylorSimplex::y2*"0.14135"
		+taylorSimplex::y3*"0.14135"
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

int C623668799() // III.App.4.6.6, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*
		  (interval("-0.28665")+interval("-0.2")*interval("6")
			+interval("-0.048")*interval("6"))
		+taylorQrtet::sol*"0.419351"
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


int C725822930() // III.App.4.6.7, 
	{
	static interval zetapt("0.1004445714270563950000");
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	// 2.25^2 = 5.0625;
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"5.0625","5.0625","5.0625"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::sol*(-zetapt)
		+taylorSimplex::unit*
		  (interval("-1.0e-6")+interval("-0.163")*interval("6")
			+interval("-0.0845696")*interval("6"))
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


int C529185470() // III.App.4.6.1', 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"-1"
		+taylorSimplex::unit*
		  (interval("0.60657")+interval("0.1781")*interval("-6.25")
			+interval("-0.356")*interval("-6"))
		+taylorSimplex::y1*"-0.356"
		+taylorSimplex::y2*"-0.356"
		+taylorSimplex::y3*"-0.356"
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

int C465988688() // III.App.4.6.2', 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);


	taylorFunction F = 
		taylorQrtet::sol
		+taylorSimplex::unit*
		  (interval("-0.61298")+interval("0.3405")*interval("6.25")
			+interval("-0.254")*interval("6"))
		+taylorSimplex::y1*"0.254"
		+taylorSimplex::y2*"0.254"
		+taylorSimplex::y3*"0.254"
		+taylorSimplex::y4*"-0.3405"
		+taylorSimplex::y5*"-0.3405"
		+taylorSimplex::y6*"-0.3405";
	F.setReducibleState(0);

	/* Note: this inequality (J<0) is an experiment designed to see whether
	   it speeds up the calculation.  J is a stronger inequality than F
	   on the domain of the inequality (0.3405->0.28). 
	   So proving J proves the inequality.
	   But when the intervals hang out beyond the actual domain, F can
	   be harder to prove.  Let's throw it in to see what happens.  */

	taylorFunction J = 
		taylorQrtet::sol
		+taylorSimplex::unit*
		  (interval("-0.61298")+interval("0.28")*interval("6.25")
			+interval("-0.254")*interval("6"))
		+taylorSimplex::y1*"0.254"
		+taylorSimplex::y2*"0.254"
		+taylorSimplex::y3*"0.254"
		+taylorSimplex::y4*"-0.28"
		+taylorSimplex::y5*"-0.28"
		+taylorSimplex::y6*"-0.28";
	J.setReducibleState(0);
	taylorFunction G =
		taylorSimplex::unit*"-6.25"
		+taylorSimplex::y4
		+taylorSimplex::y5
		+taylorSimplex::y6;
	G.setReducibleState(0);
	taylorFunction H=
		taylorSimplex::unit*"6.13"
		+taylorSimplex::y1*"-1"
		+taylorSimplex::y2*"-1"
		+taylorSimplex::y3*"-1";
	H.setReducibleState(1);
	// can't call generic or generic2 now that we have 3 inequalities:
    domain x0 = x,z0 = z;
    const taylorFunction* I[4] = {&F,&G,&H,&J};
    cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,4,opt);
	}

int C932857750() // III.App.4.6.3', 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::unit*
		  (interval("-0.02004")+interval("-0.0781")*interval("6.25")
			+interval("-0.167")*interval("6"))
		+taylorSimplex::y1*"0.167"
		+taylorSimplex::y2*"0.167"
		+taylorSimplex::y3*"0.167"
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

int C254329225() // III.App.4.6.4', 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval v("4.5369"); // 2.13^2=4.5369;
	interval tz[6]={v,v,v,"6.3001","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::sol*"0.419351"
		+taylorSimplex::unit*
		  (interval("-0.27441")+interval("0.0106")*interval("6.25")
			+interval("-0.2")*interval("6"))
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


int C695882424() // III.App.4.4.1, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","8","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","6.3001","8","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"4.885"
		+taylorSimplex::y1*"0.372"
		+taylorSimplex::y2*"-0.465"
		+taylorSimplex::y3*"-0.465"
		+taylorSimplex::y5*"-0.465"
		+taylorSimplex::y6*"-0.465";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}

int C797742838() // III.App.4.4.2, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","8","4","4"};
	x = domain::lowerD(tx);
	interval h("5.1076"); // = 2.26^2, see $c/cplex/cplex.18h.sum.
	interval tz[6]={h,h,h,"21.21","6.3001","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorSimplex::lowVorVc 
		+taylorSimplex::unit*"-0.9978"
		+taylorSimplex::y2*"0.06"
		+taylorSimplex::y3*"0.06"
		+taylorSimplex::y5*"0.185"
		+taylorSimplex::y6*"0.185";
	F.setReducibleState(0);
	taylorFunction G = 
		taylorSimplex::dih*"-1"
		+taylorSimplex::unit*"2.12";
	G.setReducibleState(1);
	// can't call prove::generic on this one because of dih<2.12 constraint.
	domain x0 = x,z0 = z;
    const taylorFunction* I[2] = {&F,&G};
    cellOption opt;
	opt.setDihMax(2.12001);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt);
	}

int C721072542() // III.App.4.4.3, 
	{
	domain x,z;
	interval tx[6]={"4","4","4","4","4","4"};
	x = domain::lowerD(tx);
	interval tz[6]={"6.3001","6.3001","4","4","4","6.3001"};
	z = domain::upperD(tz);
	taylorFunction F = 
		taylorQrtet::quo*"-1"
		+taylorSimplex::unit*"0.06333"
		+taylorSimplex::y1*"-0.00758"
		+taylorSimplex::y2*"-0.0115"
		+taylorSimplex::y6*"-0.0115";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}


main()
	{
	selfTest();
	/*
	if (C619245724())
		cout << "C619245724 done"; else cout << "NO!" ;
		cout << endl;
	if (C678284947())
		cout << "C678284947 done"; else cout << "NO!" ;
		cout << endl;
	if (C970731712())
		cout << "C970731712 done"; else cout << "NO!" ;
		cout << endl;
	if (C921602098())
		cout << "C921602098 done"; else cout << "NO!" ;
		cout << endl;
	if (C338482233())
		cout << "C338482233 done"; else cout << "NO!" ;
		cout << endl;
	if (C47923787())
		cout << "C47923787done"; else cout << "NO!" ;
		cout << endl;
	if (C156673846())
		cout << "C156673846 done"; else cout << "NO!" ;
		cout << endl;
	if (C363044842())
		cout << "C363044842 done"; else cout << "NO!" ;
		cout << endl;
	if (C68229886())
		cout << "C68229886 done"; else cout << "NO!" ;
		cout << endl;
	if (C996335124())
		cout << "C996335124 done"; else cout << "NO!" ;
		cout << endl;
	if (C722658871())
		cout << "C722658871 done"; else cout << "NO!" ;
		cout << endl;
	if (C226224557())
		cout << "C226224557 done"; else cout << "NO!" ;
		cout << endl;
	if (C914585134())
		cout << "C914585134 done"; else cout << "NO!" ;
		cout << endl;
	if (C296182719())
		cout << "C296182719 done"; else cout << "NO!" ;
		cout << endl;
	if (C538860011())
		cout << "C538860011 done"; else cout << "NO!" ;
		cout << endl;
	if (C886673381())
		cout << "C886673381 done"; else cout << "NO!" ;
		cout << endl;
	if (C681494013())
		cout << "C681494013 done"; else cout << "NO!" ;
		cout << endl;
	if (C250597127())
		cout << "C250597127 done"; else cout << "NO!" ;
		cout << endl;
	if (C357108142()) 
		cout << "C357108142 done"; else cout << "NO!" ;
		cout << endl;
	if (C706389670()) 
		cout << "C706389670 done"; else cout << "NO!" ;
		cout << endl;
	if (C229576653()) 
		cout << "C229576653 done"; else cout << "NO!" ;
		cout << endl;
	if (C141552816())
		cout << "C141552816 done"; else cout << "NO!" ;
		cout << endl;
	if (C842944296())
		cout << "C842944296 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C675811884())
		cout << "C675811884 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C351282394())
		cout << "C351282394 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C310454325())
		cout << "C310454325 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl; 
	if (C570886957())
		cout << "C570886957 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C684634355())
		cout << "C684634355 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C525219062())
		cout << "C525219062 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C833691633())
		cout << "C833691633 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C600504426())
		cout << "C600504426 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C84621256())
		cout << "C84621256 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C702064613())
		cout << "C702064613 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C946080966())
		cout << "C946080966 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C235983060())
		cout << "C235983060 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C257870816())
		cout << "C257870816 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C262640426())
		cout << "C262640426 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C211766431())
		cout << "C211766431 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C702861263())
		cout << "C702861263 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C255518878())
		cout << "C255518878 done"; else cout << "NO!" ;
		error::printTime();
		cout << endl;
	if (C584917623())
		cout << "C584917623 done"; else cout << "NO!" ;
		cout << endl;
	if (C190861218())
		cout << "C190861218 done"; else cout << "NO!" ;
		cout << endl;
	if (C957853434())
		cout << "C957853434 done"; else cout << "NO!" ;
		cout << endl;
	if (C880803585())
		cout << "C880803585 done"; else cout << "NO!" ;
		cout << endl;
	if (C193930450())
		cout << "C193930450 done"; else cout << "NO!" ;
		cout << endl;
	if (C623668799())
		cout << "C623668799 done"; else cout << "NO!" ;
		cout << endl;
	if (C725822930())
		cout << "C725822930 done"; else cout << "NO!" ;
		cout << endl;
	if (C529185470())
		cout << "C529185470 done"; else cout << "NO!" ;
		cout << endl;

	if (C465988688())
		cout << "C465988688 done"; else cout << "NO!" ;
		cout << endl;
	if (C932857750())
		cout << "C932857750 done"; else cout << "NO!" ;
		cout << endl;
	if (C254329225())
		cout << "C254329225 done"; else cout << "NO!" ;
		cout << endl;


	if (C695882424())
		cout << "C695882424 done"; else cout << "NO!" ;
		cout << endl;
	*/
	if (C797742838())
		cout << "C797742838 done"; else cout << "NO!" ;
		cout << endl;
	/*
	if (C721072542())
		cout << "C721072542 done"; else cout << "NO!" ;
		cout << endl;
	*/

	error::printTime();
	}
