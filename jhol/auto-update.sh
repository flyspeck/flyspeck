#!/bin/bash
FLYSPECK_SOURCE=`readlink --canonicalize --no-newline $BASH_SOURCE`
FLYSPECK_DIR=`dirname $FLYSPECK_SOURCE`
cd $FLYSPECK_DIR

svn update --non-interactive ..

  if [ -a "$T2.cr" ]; then
    echo "flyspeck is current."
  else   
    exec ./checkpoint_flyspeck
  fi
