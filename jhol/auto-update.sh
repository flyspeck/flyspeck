#!/bin/bash
JHOL_DIR=`dirname $BASH_SOURCE`
svn update $JHOL_DIR/..
T2=`svnversion $JHOL_DIR/..`


  if [ -a "$T2.cr" ]; then
    echo "flyspeck is current."
  else   
    exec ./checkpoint_flyspeck
  fi
