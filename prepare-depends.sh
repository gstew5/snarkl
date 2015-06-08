#!/bin/sh
# This script fetches, builds and locally installs Joshua Kroll's fork of libsnark.
# (Adapted from https://github.com/scipr-lab/libsnark.)

set -x -e

DEPSRC=./depsrc
DEPINST=./depinst

mkdir -p $DEPINST
mkdir -p $DEPSRC

cd $DEPSRC
[ ! -d libsnark ] && git clone git://github.com/jkroll/libsnark
cd libsnark
./prepare-depends.sh
make
cd ..
cd ..
cp -rv $DEPSRC/libsnark $DEPINST/

