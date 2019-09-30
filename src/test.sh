#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

make -C $THIS_DIR stdlib/lin.intr test.exe > /dev/null 2>&1
$THIS_DIR/_build/default/test.exe -intrinsics $THIS_DIR/stdlib/lin.intr "$@"
