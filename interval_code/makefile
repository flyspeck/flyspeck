# for Silicon Graphics cc compiler, -O2 for optimization, -g for debugging
#CC = CC
#CCOPTS1 = -g -OPT:IEEE_comparisons:IEEE_arithmetic=1:roundoff=0:fold_arith_limit=2000 

# for g++ on SUNS;  option -O2 optimize, -g debug
# problem with -O2 and inline rounding mode on solaris, 
# code migrates past inline.  Let's keep it at -O1 optimization.
# -O1 for optimization
##L = -L/usr/local/gcc-2.7.2/lib
#CC     = g++
#CCOPTS1 = -g -W -Wall -fno-defer-pop -L/usr/local/lib 


# solaris: -O2 for optimization...
CC = g++
#L = 
CCOPTS1 = -g 
CCOPTS_NORM= -O1
CCOPTS2 = -O2

error.o : error.h interval.h error.cc #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c error.cc
interval.o : interval.h interval_inline.h error.h interval.cc #Stay at O1
	$(CC) $(CCOPTS1) $(CCOPTS_NORM) -c interval.cc
secondDerive.o : secondDerive.cc secondDerive.h error.h interval.h interval_inline.h #Stay at O1
	$(CC) $(CCOPTS1) $(CCOPTS_NORM) -c secondDerive.cc 
lineInterval.o : lineInterval.h lineInterval.cc interval.h \
	error.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c lineInterval.cc 
taylorInterval.o : taylorInterval.cc error.h interval.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c taylorInterval.cc
recurse.o : recurse.h recurse.cc taylorInterval.h error.h interval.h interval_inline.h #Can be opt. in level2
	$(CC) $(CCOPTS1) $(CCOPTS2) -c recurse.cc 
recurseQ.o : recurse.h recurseQ.cc taylorInterval.h error.h interval.h interval_inline.h 
	$(CC) $(CCOPTS1) -c recurseQ.cc 
trig.o : recurse.h trig.cc trig.h taylorInterval.h error.h interval.h interval_inline.h 
	$(CC) $(CCOPTS1) -c trig.cc 


testit: test.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) test.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o testit -lm $(L)

part3 : part3.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3 -lm $(L)

part3more : part3more.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3more.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3more -lm $(L)

part3t : part3t.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3t.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3t -lm $(L)

# same as part3t :

part3tx : part3t.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3t.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3tx -lm $(L)

# same as part3t :
part3ty : part3t.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3t.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3ty -lm $(L)

# same as part3t :
part3tz : part3t.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3t.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3tz -lm $(L)

# same as part3t :
part3tw : part3t.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o
	$(CC) $(CCOPTS1) part3t.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part3tw -lm $(L)

part3oData.o : part3oData.cc
	$(CC) $(CCOPTS1) -c part3oData.cc
part3oDataSupp.o : part3oDataSupp.cc
	$(CC) $(CCOPTS1) -c part3oDataSupp.cc

part3o : part3o.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o part3oData.o part3oDataSupp.o
	$(CC) $(CCOPTS1) part3o.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o part3oData.o part3oDataSupp.o -o part3o -lm $(L)

part3ox : part3o.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o part3oData.o part3oDataSupp.o
	$(CC) $(CCOPTS1) part3o.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o part3oData.o part3oDataSupp.o -o part3ox -lm $(L)

part4 : part4.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o #This can be put together at 02
	$(CC) $(CCOPTS1)$(CCOPTS2) part4.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part4 -lm $(L)

part4sec1 : part4sec1.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o #This can be put together at 02
	$(CC) $(CCOPTS1)$(CCOPTS2) part4sec1.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part4sec1 -lm $(L)

partK : partK.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o #This can be put together at 02
	$(CC) $(CCOPTS1)$(CCOPTS2) partK.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o partK -lm $(L)

part4sec10 : part4sec10.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o #This can be put together at 02
	$(CC) $(CCOPTS1)$(CCOPTS2) part4sec10.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part4sec10 -lm $(L)

part4sec23 : part4sec23.cc error.h error.o interval.h interval.o lineInterval.h \
	lineInterval.o secondDerive.h secondDerive.o taylorInterval.o \
	recurse.h recurse.o #This can be put together at 02
	$(CC) $(CCOPTS1)$(CCOPTS2) part4sec23.cc error.o interval.o lineInterval.o secondDerive.o taylorInterval.o recurse.o -o part4sec23 -lm $(L)

secondDerive : secondDerive.cc error.h interval.h interval_inline.h \
	error.o interval.o io.o
	$(CC) $(CCOPTS1) secondDerive.cc error.o interval.o io.o -o secondDerive -lm

3d : 3d.cc error.h interval.h interval_inline.h
	$(CC) $(CCOPTS1) 3d.cc error.o interval.o -o 3d -lm
3dx : 3d.cc error.h interval.h interval_inline.h
	$(CC) $(CCOPTS1) 3d.cc error.o interval.o -o 3dx -lm
3dy : 3d.cc error.h interval.h interval_inline.h
	$(CC) $(CCOPTS1) 3d.cc error.o interval.o -o 3dy -lm

