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
%.o :   %.cc $(DEPS)
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

numerical.o : numerical.h numerical.cc
	$(CC) $(CCOPTS1) -c  numerical.cc

# linkable version:
2065952723B.o : 2065952723A.h 2065952723A.cc
	$(CC) $(CCOPTS1) -c  2065952723A.cc -o 2065952723B.o


#examples

#local_fan.o : local_fan.cc  $(DEPS)
#	$(CC) $(CCOPTS1) local_fan.cc $(DOTS)  -o local_fan.o

maytest.o : maytest.cc  $(DEPS) numerical.cc
	$(CC) $(CCOPTS1) maytest.cc $(DOTS)  -o maytest.o

feb16_phelan_weaire_text.o : feb16_phelan_weaire_text.cc  $(DEPS) numerical.cc
	$(CC) $(CCOPTS1) feb16_phelan_weaire_text.cc $(DOTS)  -o feb16_phelan_weaire_text.o


#tame_hypermap.o : tame_hypermap.cc  $(DEPS)
#	$(CC) $(CCOPTS1) tame_hypermap.cc $(DOTS)  -o tame_hypermap.o


#glpk_ineq.o : glpk_ineq.cc  $(DEPS)
#	$(CC) $(CCOPTS1) glpk_ineq.cc $(DOTS)  -o glpk_ineq.o

#further_results.o : further_results.cc  $(DEPS)
#	$(CC) $(CCOPTS1) further_results.cc $(DOTS)  -o further_results.o


