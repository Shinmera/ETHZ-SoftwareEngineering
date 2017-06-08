#!/bin/bash

base=$(pwd)
export CLASSPATH=.:$base/soot-2.5.0.jar:$base/apron.jar:$base/gmp.jar
export LD_LIBRARY_PATH=$base/

mkdir -p bin
javac -d bin src/*.java
javac -d bin src/ch/ethz/sae/*.java




