#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

# echo $THIS_DIR
# echo $THIS_DIR/_build/default/counterexample.exe "$@" -cex-trace=__tmp__eldarica__cex -intrinsics $THIS_DIR/stdlib/lin.intr

# make -C $THIS_DIR stdlib/lin.intr test.exe > /dev/null 2>&1
if [ $? -ne 0 ]; then
	echo "! WARNING: BUILD FAILED" >&2
fi
rm -f __tmp__eldarica__cex
rm -f __tmp__eldarica__cons
$THIS_DIR/_build/default/test.exe -intrinsics $THIS_DIR/stdlib/lin.intr -save-cons=__tmp__eldarica__cons -solver eldarica -timeout 0 -dry-run "$@" -mode unified &> /dev/null
echo "First run ownershp slice generation"
$THIS_DIR/_build/default/counterexampleOwnership.exe -intrinsics $THIS_DIR/stdlib/lin.intr "$@"
echo "Running eldarica...."
eld -t:120 -horn -cex -hsmt __tmp__eldarica__cons > __tmp__eldarica__cex
head -n 1 __tmp__eldarica__cex
echo "Trying to extract trace...."
sed -i -e "/mu/d" __tmp__eldarica__cex

$THIS_DIR/_build/default/counterexample.exe "$@" -cex-trace=__tmp__eldarica__cex -intrinsics $THIS_DIR/stdlib/lin.intr
