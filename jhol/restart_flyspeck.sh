#!/bin/bash
cd `dirname $BASH_SOURCE`
cr_restart --no-restore-pid -S 2 `svnversion ..`.cr