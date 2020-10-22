#!/bin/sh
cd ..
dune build typecheck.exe && ./_build/default/typecheck.exe -intrinsics stdlib/lin.intr alex-tests/recursive-object.imp
# dune build test.exe && ./_build/default/test.exe -intrinsics stdlib/lin.intr alex-tests/recursive-object.imp
