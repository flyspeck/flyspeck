#!/bin/bash
JHOL_SOURCE=`readlink --canonicalize --no-newline $BASH_SOURCE`
JHOL_DIR=`dirname $JHOL_SOURCE`
cd $JHOL_DIR

svn update ../text_formalization
T2=`svnversion ../text_formalization`


  if [ -a "$T2.cr" ]; then
    echo "flyspeck is current."
  else   
    exec ./checkpoint_flyspeck
  fi
