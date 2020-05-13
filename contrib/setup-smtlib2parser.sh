#!/bin/bash

SMTLIB2PARSER_VERSION=982e5952ee394e9a8e1f0c6200c9e51050ee1e66

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/smtlib2parser" ]; then
    cd $DEPS
    git clone --depth 1 https://github.com/zhanghongce/smtlib2parser smtlib2parser
    cd smtlib2parser
    git checkout -f $SMTLIB2PARSER_VERSION
    CFLAGS="" ./configure.sh --static
    cd build
    make -j${NPROC}
    cd $DIR
else
    echo "$DEPS/smtlib2parser already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/smtlib2parser/build/src/libsmtparser.a ] ; then \
    echo "It appears smtlib2parser was successfully built in $DEPS/smtlib2parser/build/lib."
    echo "You may now build cosa2 with: ./configure.sh && cd build && make"
else
    echo "Building smtlib2parser failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Boolector/smtlib2parser.git"
    exit 1
fi

