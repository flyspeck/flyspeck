#!/bin/sh

g++ -Wall Kepler_2009_genGraphDat.cpp -o gengraphdat
ghc process.hs -o process
