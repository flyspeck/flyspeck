

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

  enum n298 { neg_deltaA, neg_deltaB, neg_num1, pos_num1, neg_num2, reflexAB,
	    angleYA, angleYB, angleYAB, neg_rat1, pos_rat1, neg_rat2, neg_rat2_A0, eulerB, 
	    split };

  static n298 setStrategy298(double xmin[9],double xmax[9],double* cut) ;

};
