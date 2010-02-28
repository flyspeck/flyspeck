#Makefile for cfsqp testing of inequalities for the Kepler conjecture.


# Tutorial on make:
# $@ file to be made
# $< file that caused the action
# $? names of the changed dependents
# $* prefix shared by target and dependent.

#for Silicon graphics cc compiler
#CC = CC
#CCOPTS1 = -O2 -g -dalign

#for g++ on SUNS
CC = g++
CCOPTS1 = -g -O2

# for windows cygwin
#CC = gcc
#CCOPTS1 = -dalign

DOTS=Minimizer.o numerical.o sqp/qld.o sqp/cfsqp.o sqp/cfsqpAdapter.o
DEPS=Minimizer.h Minimizer.cc numerical.h numerical.cc

# general rule
*.o :   *.cc $(DEPS)
	$(CC) $(CCOPTS1) $*.cc $(DOTS) -o $@


#files in the cfsqp distribution
sqp/cfsqp.o : sqp/cfsqp.c sqp/cfsqpusr.h
	$(CC) $(CCOPTS1) -c sqp/cfsqp.c
	mv cfsqp.* sqp

sqp/qld.o : sqp/qld.c 
	$(CC) $(CCOPTS1) -c sqp/qld.c
	mv qld.* sqp

#adapter classes for cfsqp
sqp/cfsqpAdapter.o : sqp/cfsqpAdapter.c sqp/cfsqpusr.h
	$(CC) $(CCOPTS1) -c sqp/cfsqpAdapter.c
	mv cfsq*.* sqp

Minimizer.o : Minimizer.h Minimizer.cc
	$(CC) $(CCOPTS1) -c Minimizer.cc

#files containing Kepler conjecture functions
numerical.o : numerical.h numerical.cc
	$(CC) $(CCOPTS1) -c  numerical.cc

morefn.o : morefn.h morefn.cc numerical.h 
	$(CC) $(CCOPTS1) -c  morefn.cc   
	rm morefn.cc.*

constant.o : constant.h constant.cc
	$(CC) $(CCOPTS1) -c constant.cc


#examples
example1.o : example1.cc Minimizer.h Minimizer.cc
	$(CC) $(CCOPTS1) example1.cc $(DOTS) -o example1.o

test.o : test.cc numerical.cc numerical.h
	$(CC) $(CCOPTS1) test.cc  numerical.o  -o test.o

marchal.o : marchal.cc  $(DEPS)
	$(CC) $(CCOPTS1) marchal.cc $(DOTS)  -o marchal.o


local_fan.o : local_fan.cc  $(DEPS)
	$(CC) $(CCOPTS1) local_fan.cc $(DOTS)  -o local_fan.o

tame_hypermap.o : tame_hypermap.cc  $(DEPS)
	$(CC) $(CCOPTS1) tame_hypermap.cc $(DOTS)  -o tame_hypermap.o

glpk_ineq.o : glpk_ineq.cc  $(DEPS)
	$(CC) $(CCOPTS1) glpk_ineq.cc $(DOTS)  -o glpk_ineq.o

further_results.o : further_results.cc  $(DEPS)
	$(CC) $(CCOPTS1) further_results.cc $(DOTS)  -o further_results.o

nonlin.o : nonlin.cc  $(DEPS)
	$(CC) $(CCOPTS1) nonlin.cc $(DOTS)  -o nonlin.o




#reinhardt
reinhardtlib.o : reinhardtlib.h reinhardtlib.cc
	$(CC) $(CCOPTS1) -c reinhardtlib.cc

reinhardt1.o : reinhardt1.cc reinhardtlib.cc reinhardtlib.h $(DEPS)
	$(CC) $(CCOPTS1) reinhardt1.cc $(DOTS) reinhardtlib.o -o reinhardt1.o

reinhardtBC.o : reinhardtBC.cc reinhardtlib.cc reinhardtlib.h $(DEPS)
	$(CC) $(CCOPTS1) reinhardtBC.cc $(DOTS) reinhardtlib.o -o reinhardtBC.o