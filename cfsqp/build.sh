#!/bin/bash
make sqp/qld.o
make sqp/cfsqp.o
make sqp/cfsqpAdapter.o
make Minimizer.o
make numerical.o
make glpk_ineq.o
make 2065952723B.o
#./glpk_ineq.o  #this fails at the moment

