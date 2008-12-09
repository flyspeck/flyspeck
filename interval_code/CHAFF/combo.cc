//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


#include <iomanip.h>
#include <iostream.h>
extern "C"
{
#include <math.h>
#include <stdlib.h>
}
#include "error.h"
#include "interval.h"
#include "taylorInterval.h"

combo operator+(combo a,combo b)
	{
	int i,j,match;
	for (i=0;i<b.length;i++)
		{
		match=0;
		for (j=0;j<a.length;j++)
			{
			if (match) continue;
			if ((a.fnarray[j]==b.fnarray[i])
				&&(a.secarray[j]==b.secarray[i]))
				{
				a.constant[j]=a.constant[j]+b.constant[i];
				match=1;
				}
			}
		if (!match)
			{
			a.fnarray[a.length]=b.fnarray[i];
			a.secarray[a.length]=b.secarray[i];
			a.constant[a.length]=b.constant[i];
			a.length++;
			if (a.length>=COMBO_SIZE) error_msg("array overflow");
			}
		}
	return a;
	}

combo operator-(combo a)
	{
	for (int i=0;i<a.length;i++)
		a.constant[i] = -a.constant[i];
	return a;
	}

combo operator*(interval t,combo a)
	{
	for (int i=0;i<a.length;i++)
		a.constant[i] = t*a.constant[i];
	return a;
	}

combo operator*(combo a,interval t)
	{
	for (int i=0;i<a.length;i++)
		a.constant[i]= t*a.constant[i];
	return a;
	}
	
combo operator-(combo a,combo b)
	{
	return a + (-b);
	}

series combo_fn(const double x[6],int* ptr)
	{
	int i;
	series t(zero);
	combo* lc = (combo*) ptr;
	for (i=0;i<lc->length;i++) t = t+ (lc->fnarray[i])(x)*lc->constant[i];
	return t;
	}


int sec_combo(const double x[6],const double z[6],double DD[6][6],int* ptr)
	{
	int i,j,k;
	double DDj[6][6];
	combo* lc = (combo*) ptr;
	for (i=0;i<6;i++) for (j=i;j<6;j++) DD[i][j]=0.0;
	for (k=0;k<lc->length;k++)
		{
		if (!((*lc->secarray[k])(x,z,DDj))) return 0;
		for (i=0;i<6;i++) for (j=i;j<6;j++) 
			DD[i][j]= DD[i][j]+DDj[i][j]*abs(lc->constant[k]);
		}
	for (i=0;i<6;i++) for (j=0;j<i;j++) DD[i][j]=DD[j][i];
	return 1;
	}


