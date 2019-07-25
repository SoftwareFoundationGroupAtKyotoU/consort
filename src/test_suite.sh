#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

function r_test {
	./_build/default/test_suite.exe -intrinsics ./stdlib/lin.intr "$@"
}

declare -a POS_DIRS
POS_DIRS=(pre-relation challenge-problem jayhorn)

(
	cd $THIS_DIR;
	make test;
	r_test -seq-solver -pos ./positive-tests;
	r_test -pos ./positive-tests;
	for i in ${POS_DIRS[@]}; do
		r_test -pos -seq-solver ./positive-tests/$i;
	done
	r_test -pos -cfa 2 ./positive-tests/2cfa;
	r_test -neg ./negative-tests
)
