////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0_1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4cell(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m0_1() {
  double xmin[6]= {2*hmax+eps,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_1(m0_1(),"ID d0_01: Marchal GGPOS gamma4cell function, one above hmax");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_2() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {2*hmin,2*hmin,2*hmin,2*hmin,2*hmin,2*hmin};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_2(m0_2(),"ID d0_2: Marchal GGPOS gamma4cell function, all below hmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_3() {
  double xmin[6]= {2*hmin,2,2,2*hmin,2,2};
  double xmax[6]= {2*hmax,2*hmax,2*hmax,2*hmax,2*hmax,2*hmax};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_3(m0_3(),"ID d0_3: Marchal GGPOS gamma4cell function, opposite pair above hmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
Minimizer m0_4() {
  double xmin[6]= {2*hmin,2*hmin,2,2,2,2};
  double xmax[6]= {2*hmax,2*hmax,2*hmax,2*hmax,2*hmax,2*hmax};
	Minimizer M(80,6,1,xmin,xmax);
	M.func = t0_1;
	M.cFunc = smallrad;
	return M;
}
trialdata d0_4(m0_4(),"ID d0_4: Marchal GGPOS gamma4cell function, adjacent pair above hmin");

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t23(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gg1(y[0],y[1],y[2],y[3],y[4],y[5]) - (0.2147) + 0.20495 * (dih_y(y[0],y[1],y[2],y[3],y[4],y[5]));
	}
Minimizer m23() {
  double t = 2.0*hmin;
  double xmin[6]= {2.0*hmin,2,2,2,2,2};
  double xmax[6]= {2.0*hmax,t,t,sqrt(8.0),t,t};
	Minimizer M(trialcount,6,1,xmin,xmax);
	M.func = t23;
	M.cFunc = bigrady;
	return M;
}
trialdata d23(m23(),"ID TTAMHQQ: cc:6bl: d23: Marchal, gamma3cell >= 0.2147/2 - 0.20495 dih");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t24(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = gamma4wt(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.2147 + 0.20495 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m24(int i2,int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(i2),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(i2),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,1,xmin,xmax);
	M.func = t24;
	M.cFunc = smallrady;
	return M;
}
// d24 in main().

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t24a(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = ggwt1(y[0],y[1],y[2],y[3],y[4],y[5]) - 0.2147 + 0.20495 * dih_y(y[0],y[1],y[2],y[3],y[4],y[5]);
	}
Minimizer m24a(int i2,int i3,int i4,int i5,int i6) {
  double xmin[6]= {xxmin(1),xxmin(i2),xxmin(i3),xxmin(i4),xxmin(i5),xxmin(i6)};
  double xmax[6]= {xxmax(1),xxmax(i2),xxmax(i3),xxmax(i4),xxmax(i5),xxmax(i6)}; 
	Minimizer M(40,6,3,xmin,xmax);
	M.func = t24a;
	M.cFunc = bigradysmallrafy;
	return M;
}
// d24a in main().


main()
{


  // LEAVE EMPTY.
  // d24 has many cases:
  /*
for (int i2=0;i2<3;i2++)
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(i2); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
if (rady(xmin[0],xmin[1],xmin[2],xmin[3],xmin[4],xmin[5])> s2) continue;
else 
{
trialdata d24(m24(i2,i3,i4,i5,i6),"ID TTAMHQQ: 6:bl: d24: Marchal, gamma4wt >=  0.2147 - 0.2045 dih, many cases ");
}
  }
  */
  // d24a has many cases:
/*
for (int i2=0;i2<3;i2++)
for (int i3=0;i3<3;i3++)
for (int i4=0;i4<3;i4++)
for (int i5=0;i5<3;i5++)
for (int i6=0;i6<3;i6++)
  {
xmin[0]=xxmin(1); xmin[1]=xxmin(i2); xmin[2]=xxmin(i3); xmin[3]=xxmin(i4); xmin[4]=xxmin(i5); xmin[5]=xxmin(i6);
    if (radf(xmin[0],xmin[1],xmin[5])> s2) continue;
    else if (radf(xmin[0],xmin[2],xmin[4])> s2) continue;
    else 
{
trialdata d24a(m24a(i2,i3,i4,i5,i6),"ID TTAMHQQ: 6:bl: d24a: Marchal, ggwt1 >=  0.2147 - 0.2045 dih, many cases ");
}
  }
*/

}
