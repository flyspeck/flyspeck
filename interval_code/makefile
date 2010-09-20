# 

# for g++ on SUNS;  option -O2 optimize, -g debug
# problem with -O2 and inline rounding mode on solaris, 
# code migrates past inline.  Let's keep it at -O1 optimization.

# 
CC = g++
CCOPTS1 = -g 
CCOPTS_NONE = -O0
CCOPTS_NORM= -O1
CCOPTS2 = -O2

error.o : error.h interval.h error.cc #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c error.cc

interval.o : interval.h interval_inline.h error.h interval.cc #Stay at no opt.
	$(CC) $(CCOPTS1)  -c interval.cc

univariate.o : interval.h interval_inline.h error.h interval.cc univariate.h univariate.cc
	$(CC) $(CCOPTS1)  -c univariate.cc

secondDerive.o : secondDerive.cc secondDerive.h error.h \
	interval.h interval_inline.h #Stay at O1
	$(CC) $(CCOPTS1) $(CCOPTS_NORM) -c secondDerive.cc 

lineInterval.o : lineInterval.h lineInterval.cc interval.h \
	error.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c lineInterval.cc 

taylorInterval.o : taylorInterval.cc error.h interval.h univariate.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c taylorInterval.cc

recurse.o : recurse.h recurse.cc taylorInterval.h error.h \
	interval.h interval_inline.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c recurse.cc 

testit: test.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) test.cc error.o interval.o lineInterval.o \
	secondDerive.o taylorInterval.o recurse.o -o testit -lm $(L)

test_auto: test_auto.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o univariate.h univariate.o
	$(CC) $(CCOPTS1) test_auto.cc error.o interval.o lineInterval.o \
	secondDerive.o taylorInterval.o recurse.o univariate.o -o test_auto -lm $(L)

