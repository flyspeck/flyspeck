

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

  static void reset(numerical_data::case298 caseno);


  numerical_data() {
  };

  static void selfTest();

};



namespace nglobal {
  static int trialcount;
  static double v_dih_constraint;
  static double delta_a_priori;
  static double alpha;  // used in linear programs.
  static double theta; // used in lindih.
  static double eps;
  static double mid;
  static double big;
  static double extra;
};

