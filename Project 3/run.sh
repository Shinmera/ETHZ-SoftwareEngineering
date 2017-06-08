#!/bin/bash

base=$(pwd)
export CLASSPATH=.:$base/soot-2.5.0.jar:$base/apron.jar:$base/gmp.jar:$base/bin
export LD_LIBRARY_PATH=$base/

java ch.ethz.sae.Verifier "$1"
