#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

make -C $THIS_DIR stdlib/lin.intr > /dev/null 2>&1
dune exec --root=$THIS_DIR ./test.exe -- -intrinsics $THIS_DIR/stdlib/lin.intr "$@"
