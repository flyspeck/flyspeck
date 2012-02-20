// Test on Feb 16, 2012 to compute scaledVoronoi Phelan-Weaire foam.

#include <iomanip.h>
#include <iostream.h>
#include "Minimizer.h"
#include <math.h>
#include "numerical.h"

double myrand();

double findMinimumEQ(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
		     void (*cFunc)(int numargs,int which,double* x,double* ret,void*));


// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};


void printv(double* v,int n) {
  cout << "{";
  for (int i =0;i<n;i++) {
    cout << v[i] << (i==n-1 ? "};" : ",");
  }
}


double norm(double x[3]) {
  return sqrt(x[0]*x[0]+x[1]*x[1]+x[2]*x[2]);
}

double dot(double x[3],double y[3]) {
  return x[0]*y[0] + x[1]*y[1] + x[2]*y[2];
}


double angle(double x[3],double y[3]) {
  return acos(dot (x,y)/ (norm(x) * norm(y)));
}

double square(double x) {
  return x*x;
}

void add3(double x[3],double y[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] + y[i]; }
}

void scale(double s,double x[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] * s; }
}

void sub3(double x[3],double y[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] - y[i]; }
}

double dist2(double x[3],double y[3]) {
  double z[3];
  sub3(x,y,z);
  return dot(z,z);
}

double RvolAn(double x1, double x2, double x3,double x4,double x5, double x6) {
  return (x1 * (x2 + x6 - x1) * chi(x4,x5,x3,x1,x2,x6)/ 
	  (48.0 * U(x1,x2,x6) * sqrt (delta_x (x1,x2,x3,x4,x5,x6))));
}

double RsurfAn(double x1,double x2,double x3,double x4,double x5, double x6) {
  //cout << " sqrt " << sqrt(x1) << endl;
  return (RvolAn(x1,x2,x3,x4,x5,x6) * (6.0/sqrt(x1)));
}

double vol6(double x1,double x2,double x3, double x4, double x5,double x6) {
  return (RvolAn(x1,x2,x3,x4,x5,x6) + RvolAn(x1,x3,x2,x4,x6,x5) +
    RvolAn(x2,x3,x1,x5,x6,x4) + RvolAn(x2,x1,x3,x5,x4,x6) +
	  RvolAn(x3,x1,x2,x6,x4,x5) + RvolAn(x3,x2,x1,x6,x5,x4));
}

double surf6(double x1,double x2,double x3,double x4,double x5,double x6) {
  return (RsurfAn(x1,x2,x3,x4,x5,x6) + RsurfAn(x1,x3,x2,x4,x6,x5) +
    RsurfAn(x2,x3,x1,x5,x6,x4) + RsurfAn(x2,x1,x3,x5,x4,x6) +
	  RsurfAn(x3,x1,x2,x6,x4,x5) + RsurfAn(x3,x2,x1,x6,x5,x4));
}

double xp(double x1,double x2,double x6,double rho1,double rho2) {
  return (x1 * rho1 * rho1 + x2*rho2*rho2 - (x1 + x2 - x6) * rho1 * rho2);
}

double triangleArea(double x1,double x2,double x3) {
  return sqrt(U(x1,x2,x3))/4.0;
}

double Rarea(double x1,double x2,double x3) {
  return x1*(x2+x3-x1)/ (8.0 * U(x1,x2,x3));
}

// Analytic volume of the part of a  scaled Voronoi cell, inside a tetrahedron.
double vol6rho(double x1,double x2,double x3,double x4,double x5,double x6,
	       double rho1,double rho2,double rho3) {
  double x1p = x1 * rho1 * rho1;
  double x2p = x2 * rho2 * rho2;
  double x3p = x3 * rho3 * rho3;
  double x4p = xp(x2,x3,x4,rho2,rho3);
  double x5p = xp(x1,x3,x5,rho1,rho3);
  double x6p = xp(x1,x2,x6,rho1,rho2);
  return vol6(x1p,x2p,x3p,x4p,x5p,x6p);
}

double rhop(double r) {
  //  return   1.0/r;   // old rule
  return   (2.0 - r);  // correct rule.
}

double mk() {
  return (0.9 + 0.2*myrand());
}
//
void testvol6rho() {
  double x[6];
  for (int i=0;i<6;i++) { x[i] = 4.0* mk(); }
  cout << "simplex vol random: " << sqrt(delta_x(x[0],x[1],x[2],x[3],x[4],x[5]))/12.0 << endl;
  double v = vol6rho(x[0],x[1],x[2],x[3],x[4],x[5],1,1,1) +
    vol6rho(x[0],x[4],x[5],x[3],x[1],x[2],1,1,1)+
    vol6rho(x[2],x[3],x[4],x[5],x[0],x[1],1,1,1)+
    vol6rho(x[1],x[3],x[5],x[4],x[0],x[2],1,1,1);
  cout <<  "simplex sum rogers random: "<<  v << endl;
  double r12 = mk();
  double r21 = rhop(r12);
  double r13 = mk();
  double r31 = rhop(r13);
  double r14 = mk();
  double r41 = rhop(r14);
  double r23 = mk();
  double r32 = rhop(r23);
  double r24 = mk();
  double r42 = rhop(r24);
  double r34 = mk();
  double r43 = rhop(r34);
  double vv = vol6rho(4,4,4,4,4,4,1,1,1) * 4.0;
  cout.precision(4);
  cout <<  r12 << " " << r13 << " " << r14 << " " << r23 << " " << r24 << " " << r34 << endl;
  cout << " vol reg simplex: " << vv << endl;
  double ww = vol6rho(4,4,4,4,4,4,r12,r13,r14)+
    vol6rho(4,4,4,4,4,4,r21,r23,r24)+
    vol6rho(4,4,4,4,4,4,r31,r32,r34)+
    vol6rho(4,4,4,4,4,4,r41,r42,r43);
  cout << "vol reg simplex, random rho: " << ww << endl;
}

// Analytic external surface of the part of a  scaled Voronoi cell, inside a tetrahedron.
double surf6rho(double x1,double x2,double x3,double x4,double x5,double x6,
	       double rho1,double rho2,double rho3) {
  double x1p = x1 * rho1 * rho1;
  double x2p = x2 * rho2 * rho2;
  double x3p = x3 * rho3 * rho3;
  double x4p = xp(x2,x3,x4,rho2,rho3);
  double x5p = xp(x1,x3,x5,rho1,rho3);
  double x6p = xp(x1,x2,x6,rho1,rho2);
  return surf6(x1p,x2p,x3p,x4p,x5p,x6p);
}

 double det3(double x[3],double y[3],double z[3]) {
   return (-x[2]*y[1]*z[0] + x[1]*y[2]*z[0] + x[2]*y[0]*z[1] 
	   - x[0]*y[2]*z[1] - x[1]*y[0]*z[2] + x[0]*y[1]*z[2]);
 }

 double volvector(double w0[3],double w1[3],double w2[3],double w3[3],
		  double rho1,double rho2,double rho3) {
   double x1 = dist2(w0,w1);
   double x2 = dist2(w0,w2);
   double x3 = dist2(w0,w3);
   double x4 = dist2(w2,w3);
   double x5 = dist2(w1,w3);
   double x6 = dist2(w1,w2);
   return vol6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

 double surfvector(double w0[3],double w1[3],double w2[3],double w3[3],
		  double rho1,double rho2,double rho3) {
   double x1 = dist2(w0,w1);
   double x2 = dist2(w0,w2);
   double x3 = dist2(w0,w3);
   double x4 = dist2(w2,w3);
   double x5 = dist2(w1,w3);
   double x6 = dist2(w1,w2);
   return surf6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

double getrho(double rho[54],int rr[54*2][2], int c,int j) {
  for (int i=0;i<54*2;i++) {
    if (rr[i][0]==c && rr[i][1] ==j)  
      return  (i % 2 == 0 ? rho[i/2] : rhop(rho[(i-1)/2]));  // XX was 1/rho.
  }
  cout << "no match found " << c << " " << j << " " << (j % 8) << endl;
  for (int i=0;i<54*2;i++)  {
      cout << "rr " << rr[i][0] << "," << rr[i][1] << endl;
    }
  assert(1==0);
}

 // w0 cell center.
 // w[i] updated positions of other points.
 // rho[i], scaling factors.
 // k[i][0],k[i][1],k[i][2],  positions of triangles of dual polyhedron around w0,
 // n number of triangles. return the total volume,
double volcell(int c, double w0[3],double wr[27*8][3],double rho[54],int rr[54*2][2],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     double rho1 = getrho(rho,rr,c,j1);
     double rho2 = getrho(rho,rr,c,j2);
     double rho3 = getrho(rho,rr,c,j3);
     double t = volvector(w0,wr[j1],wr[j2],wr[j3],rho1,rho2,rho3);
     sum += t;
   }
   return sum;
 };;

double surfcell(int c,double w0[3],double wr[27*8][3],double rho[54],int rr[54*2][2],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     double rho1 = getrho(rho,rr,c,j1);
     double rho2 = getrho(rho,rr,c,j2);
     double rho3 = getrho(rho,rr,c,j3);
     sum += surfvector(w0,wr[j1],wr[j2],wr[j3],rho1,rho2,rho3);
   }
   return sum;
 };;

 // initial data
// 0.618 ==> volcell0 = 1.127, volcell1 = 0.88
// 0.55 ==> volcell0 = 1.03, volcell1 = 0.92.
// 0.5 ==> volcell0 = 0.9765, volcell1 = 0.9765.


 double a = 0.5; // just rough initial guess, based on golden ratio of icos.
 double v0[3]={0,0,0};
 double v1[3]={1,1,1};
 double v2[3]={1,0,a};
 double v3[3]={1,0,-a};
 double v4[3]={a,1,0};
 double v5[3]={-a,1,0};
 double v6[3]={0,a,1};
 double v7[3]={0,-a,1};

 double e1[3]={2,0,0};
 double e2[3]={0,2,0};
 double e3[3]={0,0,2};
double rhodata[54];

/*
double v0[3]= {1.2636783e-29,1.2045686e-30,-1.0347183e-29};
double v1[3]= {0.95784609,0.99577094,0.95634404};
double v2[3]= {0.89680352,0.050193764,0.4993136};
double v3[3]= {0.94723366,0.024297626,-0.45703026};
double v4[3]= {0.54009954,0.99867927,-0.029991868};
double v5[3]= {-0.4177464,0.98541406,-0.042731882};
double v6[3]= {-0.061042457,0.49483768,0.92635215};
double v7[3]= {-0.084961997,-0.46280176,0.91361228};
double e1[3]= {1.9156921,-2.8573286e-29,2.564198e-29};
double e2[3]= {0.074349574,1.9142493,5.7088693e-29};
double e3[3]= {-0.074349553,0.077292997,1.9126882};
double rhodata[54]={1.522,1.103,0.6575,0.9346,1.103,1.522,0.6575,0.9346,1.103,1.522,0.9346,0.6575,0.9346,1.522,1.103,1.103,0.6575,1.522,1.522,0.9346,0.6575,0.9346,0.6575,1.103,1.061,0.8667,1.563,1.467,1.181,0.9427,1.154,0.8466,0.6817,0.64,1.467,1.154,1.061,0.8667,0.8466,0.6817,1.181,0.9427,1.154,1.467,1.563,0.8667,0.6399,1.061,0.9427,1.181,0.6817,0.8466,0.64,1.563};
*/

/*
double v0[3]= {1.249546520487602e-29,1.363073130469286e-30,-8.652534462582352e-30};
double v1[3]= {0.9578462891065259,0.9957710839131031,0.9563439339803133};
double v2[3]= {0.8968040179717008,0.05019411997166183,0.4993136387484596};
double v3[3]= {0.9472338915338402,0.02429779796335755,-0.4570303303005401};
double v4[3]= {0.5400996129991386,0.9986793566845534,-0.0299918637193601};
double v5[3]= {-0.4177467752696629,0.9854141663434376,-0.04273181793038935};
double v6[3]= {-0.06104236310613127,0.4948379308445401,0.9263520393343948};
double v7[3]= {-0.084961856115506,-0.4628012966896211,0.9136119966107727};
double e1[3]= {1.915692718410936,-2.857712033821256e-29,2.546648003386885e-29};
double e2[3]= {0.07434921093376495,1.914249101803869,5.608859526891218e-29};
double e3[3]= {-0.07434937112448044,0.0772933170308116,1.912687849240745};
double rhodata[54]={1.521799421490913,1.102518705102681,0.6575403449391205,0.9345989592975497,1.102517253748096,1.521797962370194,0.6575404811489994,0.9346000125813198,1.102518322654512,1.521798085883209,0.9345987909999612,0.6575398715447847,0.9345993440807393,1.521798998086637,1.102517402985437,1.102519027365123,0.6575405295469843,1.521798866408924,1.521797505670897,0.9346000659387569,0.6575399314110395,0.9345986007446667,0.6575400312204724,1.102518056328621,1.060802780167991,0.8667336557143136,1.56262219894083,1.466930201283263,1.181179763481318,0.9426816988110812,1.153757902155466,0.8466107929528783,0.6816959273109794,0.6399499436053115,1.466929870971007,1.153757068120664,1.060803345457239,0.8667338852263513,0.8466102029907957,0.6816956417254598,1.181180072818313,0.9426823133909306,1.153757621050262,1.466930502642801,1.562620470203279,0.8667327899041465,0.6399506860472779,1.060802129115654,0.9426828995122184,1.181181467307026,0.6816954567518102,0.8466103933221443,0.6399502179583719,1.562621424165735};
*/

// init once.  24=max number of dual triangles.
 int kk[8][24][3];   // kk[i][j] is a triple of indices of dual triangle face j of cell i. <=> vertex of sc.Vor.
 int nn[8]; // nn[i] is number of dual triangles (i.e. scVor vertices) on cell i.  (12 faces=>(nn=20, etc.)).
int  rr[54*2][2]; // {i,j} :  wi[i],ww[j] . rho[index/2]^{-1}.   inverse when index is odd. 
// runs over faces in fun. domain, indices for rhof.

 // global dynamic data

double wi[8][3];  // cell centers.
double f[3][3];  // lattice generators.

double rhof[54]; // number of shared faces in fundamental domain (2 x 12 + 6 x 14)/2.

 
 void initwif() {
   for (int i =0;i<3;i++) for (int j=0;j<3;j++) {
       f[i][j] = (i==0 ?e1[j] : (i==1 ? e2 [j] : e3[j]));
     }
   for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
       switch (i) {
       case 0 : wi[i][j] = v0[j]; break;
       case 1 : wi[i][j] = v1[j]; break;
       case 2 : wi[i][j] = v2[j]; break;
       case 3 : wi[i][j] = v3[j]; break;
       case 4 : wi[i][j] = v4[j]; break;
       case 5 : wi[i][j] = v5[j]; break;
       case 6 : wi[i][j] = v6[j]; break;
       case 7 : wi[i][j] = v7[j]; break;
       default : cout << "out of bounds " << endl; break;
     }
       for (int i =0;i<54;i++) { rhodata[i]=1.0 + 0.2*myrand(); }
       for (int i=0;i<54;i++) { rhof[i]=rhodata[i];  }
 }
 }



double ww[27*8][3];  // coordinates of 8 centers, and their lattice translates by -1,0,1 in x,y,z


 void setww() {
   for (int i=0;i<3;i++) for (int j=0;j<3;j++) for (int k=0;k<3;k++)  for (int u=0;u<8;u++) {
	   double z[3]={0,0,0};
	   double s[3];
	   scale(i-1,f[0],s); add3(z,s,z);
	   scale(j-1,f[1],s); add3(z,s,z);
	   scale(k-1,f[2],s); add3(z,s,z);
	   add3(z,wi[u],z);
	   for (int p=0;p<3;p++) {
	     ww[u + 8*(i+3*j +9*k)][p] = z[p];
	   }
	 }
 }

int isnbr(double v[3],double w[3]) {
    double x1 = mabs(v[0]-w[0]), x2 = mabs(v[1]-w[1]), x3 = mabs(v[2]-w[2]);
     return ((x1 < 1.1) && (x2 < 1.1 ) &&(x3 < 1.1) &&(dist2(v,w) > 0.01) &&
	     (dist2(v,w) < 2.1));
}

int isneg(double v1[3],double v2[3],double w1[3],double w2[3]) {
  double z1[3],z2[3],s[3];
  sub3(v1,v2,z1);
  sub3(w1,w2,z2);
  add3(z1,z2,s);
  return (mabs(dot(s,s)) < 0.01);
}

int nr[8]; // number of nearest nbrs.
int ns[8][27*8]; // nearest nbrs

 void setkknn (int i) {
   int near=0;
   for (int j=0;j<27*8;j++) {
     assert(near < 27*8);
     if (isnbr(wi[i],ww[j])) {
       ns[i][near] = j; near++;
     }
   }
   nr[i]=near;
   cout << i << " has " << near << " neighbors" << endl;
   int kc = 0;
   for (int j1=0;j1<near;j1++) for (int j2=0;j2<near;j2++) for (int j3=0;j3<near;j3++) {
	 if (isnbr(ww[ns[i][j1]],ww[ns[i][j2]]) && isnbr(ww[ns[i][j2]],ww[ns[i][j3]]) && 
	     isnbr(ww[ns[i][j3]],ww[ns[i][j1]]) &&
	     (j1 < j2) && (j2 < j3)) {
	   kk[i][kc][0]=ns[i][j1]; kk[i][kc][1]=ns[i][j2]; kk[i][kc][2]=ns[i][j3]; kc++;
	 }
       }
   nn[i]=kc;
   cout << i << " has " << kc << " faces " << endl;
 }

void setrr() {
  cout << "entering set rr " << endl;
  int rc = 0;
  int N = 150;
  int table[N][2];
  for (int i=0;i<N;i++) for (int j=0;j<2;j++) {
      table[i][j] = 0;
    }
  for (int i=0;i<8;i++) for (int j=0;j<nr[i];j++) {
      assert(rc<N);
      table[rc][0] = i;
      table[rc][1] = ns[i][j];
      rc++;
    }
  int neg=0;
  for (int i=0;i<rc;i++) for (int j=i+1;j<rc;j++) {
      if (isneg(wi[table[i][0]],ww[table[i][1]],wi[table[j][0]],ww[table[j][1]]) &&
	  (table[i][0] % 8 == table[j][1] % 8) && (table[j][0] % 8 == table[i][1] % 8)) {
	for (int o = 0;o<2;o++) {
	  int k; 
	  for (int u = 0;u<2;u++) {
	    rr[2*neg+o][u] = table[ (o ? j : i) ][u];
	  }
	}
	neg++;
      }
    }
  cout << "rho faces found " << rc << endl;
  cout << "translates found " << neg << endl;
  // check integrity of  data.
 }

double totalsurface() {
  double sum = 0;
  for (int i=0;i<8;i++) {
    sum += surfcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
  }
  return sum;
}

double mu() {
  double t = totalsurface()/(8.0 * 2.0);
  return (t*t*t);
}

void mkglobal(double* x) {
    for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
      wi[i][j] = x[i + 8*j];
    }
  int offset = 8*3;
  for (int i=0;i<3;i++) for (int j=0;j<3;j++) {
      f[i][j] = x[offset+ i + 3 * j];
    }
  offset += 3*3;
  for (int i=0;i<54;i++) { 
      rhof[i] = x[offset + i];
    }
  offset += 54;
  setww();
}

double weightedmu(double* x) {
  mkglobal(x);
  double xf = 0.0; // was 1000.0
  double m = mu();
  for (int i =0;i<8;i++) {
    double t = 1.0- volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
    m += xf * t*t;
  }
  double t = det3(f[0],f[1],f[2]) - 8.0; 
  m+= xf * t * t;
  //cout << "mu " << m << endl;
  return m;
}

// this is minimized
void t1(int numargs,int whichFn,double* x,double* ret,void*) {
  *ret =  weightedmu(x);
};

// constraints 8 vol, + det3.

void cc(int numargs,int whichFn,double* x, double* ret,void*) {
  mkglobal(x);
  if (whichFn <= 8) {
    int i = whichFn - 1;
    *ret = 1.0- volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
  }
  else { *ret = det3(f[0],f[1],f[2]) - 8.0; }
}



void printglobal() {
  cout << "printing ww,f,rhof: " << endl;
  for (int i=0;i<8;i++) {
    cout << "double v" << (i) << "[3]= ";
    printv(wi[i],3);
    cout << endl;
    }
  for (int i=0;i<3;i++) {
    cout << "double e" << (i+1) << "[3]= ";
    printv(f[i],3);
    cout << endl;
  }
  cout << "double rhodata[54]=";
  cout.precision(16);
  printv(rhof,54);
}

int nearf(double xm,double x,double xM) {
  return (min (mabs(x-xm) , mabs(x-xM) )< 1.0e-8);
}

int report_near(double* xmin,double* x,double* xmax) {
  int offset=0;
  cout << "boundaries : " << endl;
  for (int i=1;i<8;i++) for (int j=0;j<3;j++) {
      int u = offset+i+8*j;
      double a = xmin[u], b = x[u], c = xmax[u];
      if (nearf(a,b,c)) { cout << " w:"<< i <<"," <<j; 
	cout << " " << a << " " << b << " " << c << endl; 
    }
    }
  cout << endl;
  offset += 8*3;
  for (int i=0;i<3;i++) for (int j=0;j<3;j++) {
      int u = offset + i + 3*j;
      double a = xmin[u], b = x[u], c = xmax[u];
      if (nearf(a,b,c) &&(j<=i))  { cout << " f:"<< i <<"," <<j; 	cout << " " << a << " " << b << " " << c << endl; }
    }
  cout << endl;
  offset += 3*3;
    for (int i=0;i<54;i++) { 
      int u = offset + i;
      double a = xmin[u], b = x[u], c = xmax[u];
      if (nearf(a,b,c)) { cout << " rh:"<< i; 	cout << " " << a << " " << b << " " << c << endl; }
    }
  cout << endl;
}

int main() {
    initwif();
    setww();
    for (int i=0;i<8;i++) {
      setkknn(i); }
    setrr();
    int sz = 8*3+3*3+54;
    double xmin[sz];
    double xmax[sz];
    double x[sz];
    int offset = 0;
    // set ww
    double wslack = 0.1;
    for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
	xmin[offset + i + 8*j] = wi[i][j] - wslack;
	xmax[offset + i + 8*j] = wi[i][j] + wslack;
	x[offset + i + 8*j] = wi[i][j] ;
      }
    {
      int i=0;
      for (int j=0;j<3;j++) {
	xmin[offset+ i + 8*j] = wi[i][j];
	xmax[offset+ i + 8*j] = wi[i][j];
      }
    }
    offset += 8*3;
    // set f
    double fslack = 0.1;
    for (int i=0;i<3;i++) for (int j=0;j<3;j++) {
	int u = offset + i + 3 * j;
	x[u] = (i==0 ? e1[j]  : (i==1 ? e2[j] : e3[j]));
	xmin[u] = (j <= i ? x[u] - fslack : x[u]);
	xmax[u] = (j <= i ? x[u] + fslack: x[u]);
      }
    offset += 3*3;
    // set rho.
    double rhoslack = 1.1;
    for (int i=0;i<54;i++) { 
      xmin[offset + i] = rhodata[i]/rhoslack;
	xmax[offset + i] = rhodata[i]*rhoslack;
	x[offset + i] = rhodata[i];
      }
    offset += 54;
    int trialcount=5;
    assert(offset ==sz);

    double e[1];
    t1(0,0,x,e,0);

    // do minimization
    Minimizer M(trialcount,offset,9,xmin,xmax);
    M.func = t1;
    M.cFunc = cc;
    // trialdata d21(M,"xxx");
    //for (int i=0;i<offset;i++) { x[i] = M.x[i]; }

    for (int i=0;i<9;i++) {
      double r[1];
      cc(offset,i+1,x,r,0);
      mkglobal(x);
      cout << "constraint " << i << " is " << r[0] << endl;
    }

    std::cout << std::endl << std::endl;
    std::cout.precision(6);
    cout << "// NEW PASS ON PHELAN-WEAIRE: " << endl;
    cout << "t1 value before optimization = " << e[0] << endl;
    mkglobal(x);
    printglobal();
    cout << endl << endl << "mu " << mu() << endl;
    double totvol = 0.0;
    double totsurf = 0.0;
    for (int i=0;i<8;i++) {
      mkglobal(x);
      double lvol = volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
      totvol += lvol;
      cout << "volcell " << i << " = " << lvol << endl;
    }
    cout << "total vol " << totvol << endl;
    for (int i=0;i<8;i++) {
      mkglobal(x);
      double lsurf = surfcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
      totsurf += lsurf;
      cout << "surfcell " << i << " = " << lsurf << endl;
    }
    cout << "weightedmu " << weightedmu(x) << endl;
    cout << "fslack = " << fslack << endl;
   cout << "wslack = " << wslack << endl;
    cout << "rhoslack = " << rhoslack << endl;
    report_near(xmin,x,xmax);
    cout.precision(24);
    cout << "mu " << mu() << endl;
    for (int i=0;i<30;i++) { cout << "//"; }
    cout << endl << endl;

    testvol6rho();
  }

