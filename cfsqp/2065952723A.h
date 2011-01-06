

// header for 

int getCounter();

double percent_done();

void set_rectangle(double xmin[6],double xmax[6]);

struct strategy {
  enum t { split, n1, n1m, n2m, merge };
  t mode ;
  double alpha;
  int splitvar;
};

int setStrategy206A (double xmin[6],double xmax[6],strategy& s);
