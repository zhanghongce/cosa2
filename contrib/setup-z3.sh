#!/bin/bash

Z3_VERSION=4.8.8
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps
NPROC=$(nproc)

mkdir -p $DEPS

if [ ! -d "$DEPS/z3" ]; then
    cd $DEPS
    wget https://github.com/Z3Prover/z3/archive/z3-${Z3_VERSION}.zip
    unzip z3-${Z3_VERSION}.zip -d ./
    rm z3-${Z3_VERSION}.zip
    mv z3-z3-${Z3_VERSION} z3
    cd z3
    mkdir install
    ./configure --staticlib --single-threaded --prefix=$DEPS/z3/install
    cd build
    make -j${NPROC}
    make install
    cd $DIR
else
    echo "$DEPS/z3 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/z3/install/lib/libz3.a ] ; then \
    echo "It appears smtlib2parser was successfully built in $DEPS/smtlib2parser/build/lib."
    echo "You may now build cosa2 with: ./configure.sh && cd build && make"
else
    echo "Building smtlib2parser failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Boolector/smtlib2parser.git"
    exit 1
fi

