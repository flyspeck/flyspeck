#!/bin/bash

cd GraphDat
for i in *.dat ; do 
  glpsol -m ../graph0.mod -d $i | tee ../solutions/${i}.sol > /dev/null
done
