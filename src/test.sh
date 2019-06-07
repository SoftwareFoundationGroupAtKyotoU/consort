#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

dune exec --root=$THIS_DIR ./test.exe -- -intrinsics $THIS_DIR/stdlib/lin.intr "$@"
