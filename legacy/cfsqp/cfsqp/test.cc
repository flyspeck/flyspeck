#include "numerical.h"
#include <assert.h>



int main() {
  double eps = 1.0e-8;
  assert (pi() <  3.14159265359 );
  assert (pi() >  3.14159265358 );
  assert (safesqrt(-1.0) == 0.0);
  assert (safesqrt(4.0) == 2.0);
  assert (abs(delta_x(4.1,4.2,4.3,4.4,4.5,4.6) - 163.677) < eps);
  assert (abs(sol_y(2.1,2.2,2.3,2.4,2.5,2.6) - 1.05336658087449) < eps);
  assert (abs(dih_y(2.1,2.2,2.3,2.4,2.5,2.6) -  1.1884801338917963) < eps);

  // kappa
  assert (abs(kappa(2.7, 2.2, 2.3, 2.65, 2.07, 2.05) - -0.05503752415203593) < eps);
  assert (abs(kappa_dih(2.7, 2.2, 2.3, 2.07, 2.05, 2.9) - -0.08666791826297068) < eps);
  double d=dih_y(2.7, 2.2, 2.3, 2.65, 2.07, 2.05);
  assert (abs(kappa(2.7, 2.2, 2.3,  2.65, 2.07, 2.05) - kappa_dih(2.7, 2.2, 2.3,  2.07, 2.05,d)) < eps);
}
