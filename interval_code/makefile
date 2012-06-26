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
CCLINOPT = -O0

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
	error.h #Can be opt. in level2. # 4/2012 MacBook Air requires -O0
	$(CC) $(CCOPTS1) $(CCOPTS_NONE) -c lineInterval.cc 

wide.o : wide.cc error.h interval.h univariate.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c wide.cc

taylorData.o : taylorData.cc error.h interval.h univariate.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c taylorData.cc

Lib.o : Lib.cc error.h interval.h univariate.h \
	taylorData.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c Lib.cc

legacy_simplex.o : legacy_simplex.cc legacy_simplex.h error.h interval.h univariate.h \
	taylorData.h
	$(CC) $(CCOPTS1) $(CCOPTS2) -c legacy_simplex.cc

recurse.o : recurse.h recurse.cc taylorData.h Lib.h error.h \
	interval.h interval_inline.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c recurse.cc 

test: test.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorData.o \
	taylorData.h taylorData.o legacy_simplex.h legacy_simplex.o \
	recurse.h recurse.o univariate.h univariate.o
	$(CC) $(CCOPTS1) test.cc error.o interval.o lineInterval.o \
	secondDerive.o univariate.o wide.o taylorData.o Lib.o legacy_simplex.o \
	recurse.o -o test -lm $(L)

test_auto: test_auto.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorData.o \
	recurse.h recurse.o univariate.h univariate.o wide.h wide.o \
	Lib.o Lib.h
	$(CC) $(CCOPTS1)  error.o interval.o lineInterval.o \
	secondDerive.o univariate.o wide.o taylorData.o recurse.o Lib.o \
	../cfsqp/sqp/qld.o ../cfsqp/sqp/cfsqp.o ../cfsqp/sqp/cfsqpAdapter.o \
	../cfsqp/Minimizer.o \
	../cfsqp/numerical.o ../cfsqp/2065952723_link.o \
	 test_auto.cc \
	-o  test_auto -lm $(L)


jan4_test: jan4_test.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorData.o \
	recurse.h recurse.o univariate.h univariate.o
	$(CC) $(CCOPTS1) jan4_test.cc error.o interval.o lineInterval.o \
	secondDerive.o univariate.o taylorData.o recurse.o \
	 ../cfsqp/Minimizer.o ../cfsqp/numerical.o ../cfsqp/sqp/qld.o ../cfsqp/sqp/cfsqp.o ../cfsqp/sqp/cfsqpAdapter.o ../cfsqp/2065952723B.o -o jan4_test -lm $(L)


