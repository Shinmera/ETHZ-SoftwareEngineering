#!/bin/bash

base=$(pwd)
export apron_home=$HOME/apron/japron
export CLASSPATH=.:$base/soot-2.5.0.jar:$apron_home/apron.jar:$apron_home/gmp.jar:$base/bin
export LD_LIBRARY_PATH=$apron_home/:/usr/local/lib

java ch.ethz.sae.Verifier "$1"
