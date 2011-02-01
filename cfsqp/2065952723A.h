

// header for 

class numerical_data {

 public:

  static int getCounter();

  static double percent_done();

  static void set_rectangle(double xmin[6],double xmax[6]);

  struct strategy {
    enum t { split, n1, n1m, n2m, merge };
    t mode ;
    double alpha;
    int splitvar;
  };

  static int setStrategy206A (double xmin[6],double xmax[6],strategy& s);

};
