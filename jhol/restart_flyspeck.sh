#!/bin/bash
JHOL_SOURCE=`readlink --canonicalize --no-newline $BASH_SOURCE`
JHOL_DIR=`dirname $JHOL_SOURCE`
cd $JHOL_DIR
cr_restart --no-restore-pid -S 2 `svnversion ../text_formalization`.cr