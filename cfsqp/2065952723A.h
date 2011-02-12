

// header for 

class numerical_data {

 public:

  static int getCounter();

  static double percent_done();

  static void set_rectangle(double xmin[],double xmax[],int size);

  struct strategy {
    enum t { split, n1, n1m, n2m, merge };
    t mode ;
    double alpha;
    int splitvar;
  };

  static int setStrategy206A (double xmin[6],double xmax[6],strategy& s);

  enum n298 { neg_deltaA, small_deltaA, neg_deltaB, big_dihY, 
	      neg_num1, pos_num1, neg_num2, reflexAB,delta4Y,
	      angleYA, angleYB, angleYAB, neg_rat1, rat_combo, pos_rat1, neg_rat2, neg_rat2_A0, neg_rat2_B0,
	      eulerB, solidB,
	      split };

  enum case298 { top1401, dih_constraint, topit, pent_acute };

  static n298 setStrategy298(double xmin[9],double xmax[9],double* cut, case298 caseno) ;



  numerical_data() {
  };

};

class npacket {
 public:
  static int trialcount = 200;
  static const double v_dih_constraint  = 2.7458;
  static double delta_a_priori = -1.0e10;
  static double alpha=0 ;  // used in linear programs.
  static double theta=0; // used in lindih.
  static double eps=0.2;
  static double mid=10.0;
  static double big=10.0;

  reset(numerical_data::n298 caseno) {
    delta_a_priori= -1.0e10;
    eps = 0.2; mid=10.0; big=10.0;
    switch(caseno) {
    case numerical_data::top1401:  eps=0.4;  big=40; break; 
    case numerical_data::topit:  eps=0.2;  big=20; break; 
    case numerical_data::dih_constraint: delta_a_priori=21.4;  break; 
    case numerical_data::pent_acute: delta_a_priori=25.7;  break; 
    default : error::fatal("missing case");
    }
  }};;  // status: converting global to npacket..... XXD.
