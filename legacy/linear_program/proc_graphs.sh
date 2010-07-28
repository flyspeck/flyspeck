#Matthew Wampler-Doty and Thinh Nguyen
#!/bin/sh

# This is just some quick shell commands to mess with tame_graph.txt so I can
# feed it all into ocaml with minimal pain

# First download the file if we don't have it already
[ -f tame_graph.txt ] || wget  http://weyl.math.pitt.edu/hanoi2009/uploads/Kepler/tame_graph.txt

# Next process the file for use with Isabelle and for generating graph data for glpk
#echo -n "val Oct = " > process.out
tail -n +70 tame_graph.txt | grep -v "//" | sed s/\"[,]*//g | sed s/_//g | tee /tmp/kepler-stripped.out
#./process | tee -a process.out
#echo ";" >> /tmp/process.out


# Next generate the glpk files, but first make the directory if necessary
mkdir -p GraphDat
./gengraphdat

# In the future, we will have stuff for Isabelle
