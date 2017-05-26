#!/bin/bash

base=$(pwd)
export apron_home=/home/sae/apron/japron
export CLASSPATH=.:$base/soot-2.5.0.jar:$apron_home/apron.jar:$apron_home/gmp.jar
export LD_LIBRARY_PATH=$base/

mkdir -p bin
javac -d bin src/*.java
javac -d bin src/ch/ethz/sae/*.java




