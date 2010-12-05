#!/bin/bash
cd /home/joseph/Desktop
date >> auto-update.log
svn update flyspeck            
T2=`svnversion flyspeck`


  if [ -a "$T2.cr" ]; then
    echo "flyspeck is current."
  else   
    exec ./checkpoint_flyspeck
  fi
