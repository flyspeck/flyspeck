/* ========================================================================== */
/* FLYSPECK - BOOK FORMALIZATION                                              */
/*                                                                            */
/* Chapter: Nonlinear                                                  */
/* Author: Thomas C. Hales                                                    */
/* Date: 2011-01-21                                                           */
/* ========================================================================== */

// Break into cases: Inequality main_estimate_ineq.hl:'2065952723 A1'

class numerical_data {

 public:
  static int getCounter();

  static double percent_done();

  static void set_rectangle(double xmin[],double xmax[],int size);

  struct strategy {
    // split= do subdivision on variable splitvar 0..5.
    // n1 >0, n1m>0, n2m>0,
    // merge means combo (1-abs(alpha))(n2m) + alpha * n1 >0 alpha in [0,1].
    enum t { split, n1, n1m, n2m, merge };
    t mode ;
    double alpha;
    int splitvar;
  };

  static int setStrategy206A (double xmin[6],double xmax[6],strategy& s);

  numerical_data() {
  };

  static void selfTest();
};

namespace nglobal {
  static int trialcount; // global variables.
  static double alpha;  // used in linear programs.
};
